/* inflate.c — Inflate deflated data, with CFU hardware acceleration.
 *
 * Based on the original gzip inflate.c:
 *   Copyright (C) 1997-1999, 2002, 2006, 2009-2013 Free Software Foundation
 *   Original inflate algorithm: Mark Adler, "Not copyrighted 1992"
 *
 * CFU acceleration layer:
 *   All NEEDBITS / DUMPBITS / bit-peek operations are handled by the CXU
 *   via cfu_inflate.h.  No CXU state registers are used; the bit-buffer
 *   state travels in a single packed 32-bit RISC-V register between calls.
 *
 *   Packed bit-state word layout:
 *     [31:24] = bk  (number of valid bits in the buffer)
 *     [23: 0] = bb  (bit buffer, low 24 bits)
 *
 * Everything that does NOT touch the bit stream (huft_build, huft_free,
 * the sliding-window copy, CRC, I/O) is unchanged from the original.
 */

#include <config.h>
#include "tailor.h"
#include <stdlib.h>
#include "gzip.h"
#include "cxu_opt_funcs.h"

#define slide window

/* ── huft entry ─────────────────────────────────────────────────────────── */
struct huft {
  uch e;                /* extra bits / operation code */
  uch b;                /* bits in this code or subcode */
  union {
    ush n;              /* literal, length base, or distance base */
    struct huft *t;     /* pointer to next level of table */
  } v;
};

static int huft_free(struct huft *);

/* ── Window position (wp) and global bit-buffer (bb/bk) ─────────────────── */
/* wp is aliased to outcnt via the macro below, exactly as in the original.  */
#define wp outcnt
#define flush_output(w) (wp = (w), flush_window())

/* The global bit-buffer pair.  Functions copy these to a packed local state
 * at entry and flush them back at exit, just as the original used local b,k. */
static ulg      bb;   /* bit buffer           */
static unsigned bk;   /* bits in bit buffer   */

/* ── Deflate tables (unchanged) ─────────────────────────────────────────── */
static unsigned border[] = {
        16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15};

static ush cplens[] = {
        3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
        35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258, 0, 0};

static ush cplext[] = {
        0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
        3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 99, 99};

static ush cpdist[] = {
        1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
        257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
        8193, 12289, 16385, 24577};

static ush cpdext[] = {
        0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
        7, 7, 8, 8, 9, 9, 10, 10, 11, 11,
        12, 12, 13, 13};

/* ── Lookup-table parameters ─────────────────────────────────────────────── */
static int lbits = 9;
static int dbits = 6;

/* ── mask_bits[] — still needed by huft_build and by the original GETBYTE
 *   macro chain; the CXU replicates this ROM internally. ───────────────── */
static ush mask_bits[] = {
    0x0000,
    0x0001, 0x0003, 0x0007, 0x000f, 0x001f, 0x003f, 0x007f, 0x00ff,
    0x01ff, 0x03ff, 0x07ff, 0x0fff, 0x1fff, 0x3fff, 0x7fff, 0xffff
};

/* ── Byte-fetch helpers (unchanged from original) ───────────────────────── */
#define GETBYTE() \
    (inptr < insize ? inbuf[inptr++] : (wp = w, fill_inbuf(0)))

#ifdef CRYPT
  uch cc;
#  define NEXTBYTE() \
     (decrypt ? (cc = GETBYTE(), zdecode(cc), cc) : GETBYTE())
#else
#  define NEXTBYTE() (uch)GETBYTE()
#endif

/* ── CXU bit-state macros ───────────────────────────────────────────────── */
/*
 * _bs  — packed bit-state living in a local uint32_t.
 *
 * BS_INIT()  — load globals bb,bk → _bs at function entry.
 * BS_SAVE()  — flush _bs → globals bb,bk at function exit.
 *
 * NEEDBITS_HW(n)  — ensure ≥n bits are available (loops calling NEXTBYTE).
 * DUMPBITS_HW(n)  — consume n bits.
 * PEEKBITS_HW(n)  — read low n bits of bb (non-destructive).
 * HUFT_IDX(bl)    — bb & mask_bits[bl], the Huffman table row index.
 *
 * These are defined in cfu_inflate.h; repeated here as a reminder:
 *
 *   BS_DECL()      uint32_t _bs;
 *   BS_INIT()      _bs = cfu_pack(bb, bk)
 *   BS_SAVE()      bb = cfu_bb(_bs); bk = cfu_bk(_bs)
 *
 *   NEEDBITS_HW(n) while (cfu_need_check(_bs,n)) _bs=cfu_load_byte(_bs,NEXTBYTE())
 *   DUMPBITS_HW(n) _bs = cfu_dump(_bs, n)
 *   PEEKBITS_HW(n) cfu_peek(_bs, n)
 *   HUFT_IDX(bl)   cfu_huft_idx(cfu_bb(_bs), bl)
 */

/* Shorthand used inside this file only. */
#define HUFT_IDX(bl)   cfu_huft_idx(cfu_bb(_bs), (unsigned)(bl))

/* ── hufts memory tracker ────────────────────────────────────────────────── */
#define BMAX 16
#define N_MAX 288
static unsigned hufts;

/* ═══════════════════════════════════════════════════════════════════════════
 * huft_build — unchanged from original.
 * ═══════════════════════════════════════════════════════════════════════════ */
static int
huft_build(unsigned *b, unsigned n, unsigned s,
           ush *d, ush *e,
           struct huft **t, int *m)
{
  unsigned a;
  unsigned c[BMAX+1];
  unsigned f;
  int g, h;
  register unsigned i, j;
  register int k;
  int l;
  register unsigned *p;
  register struct huft *q;
  struct huft r;
  struct huft *u[BMAX];
  unsigned v[N_MAX];
  register int w;
  unsigned x[BMAX+1];
  unsigned *xp;
  int y;
  unsigned z;

  memzero(c, sizeof(c));
  p = b; i = n;
  do {
    c[*p]++;
    p++;
  } while (--i);

  if (c[0] == n) {
    q = (struct huft *) malloc(3 * sizeof *q);
    if (!q) return 3;
    hufts += 3;
    q[0].v.t = (struct huft *) NULL;
    q[1].e = 99; q[1].b = 1;
    q[2].e = 99; q[2].b = 1;
    *t = q + 1;
    *m = 1;
    return 0;
  }

  l = *m;
  for (j = 1; j <= BMAX; j++) if (c[j]) break;
  k = j;
  if ((unsigned)l < j) l = j;
  for (i = BMAX; i; i--) if (c[i]) break;
  g = i;
  if ((unsigned)l > i) l = i;
  *m = l;

  for (y = 1 << j; j < i; j++, y <<= 1)
    if ((y -= c[j]) < 0) return 2;
  if ((y -= c[i]) < 0) return 2;
  c[i] += y;

  x[1] = j = 0;
  p = c + 1; xp = x + 2;
  while (--i) { *xp++ = (j += *p++); }

  p = b; i = 0;
  do {
    if ((j = *p++) != 0)
      v[x[j]++] = i;
  } while (++i < n);
  n = x[g];

  x[0] = i = 0;
  p = v;
  h = -1;
  w = -l;
  u[0] = (struct huft *)NULL;
  q   = (struct huft *)NULL;
  z   = 0;

  for (; k <= g; k++) {
    a = c[k];
    while (a--) {
      while (k > w + l) {
        h++;
        w += l;
        z = (z = g - w) > (unsigned)l ? l : z;
        if ((f = 1 << (j = k - w)) > a + 1) {
          f -= a + 1;
          xp = c + k;
          if (j < z)
            while (++j < z) {
              if ((f <<= 1) <= *++xp) break;
              f -= *xp;
            }
        }
        z = 1 << j;
        if ((q = (struct huft *)malloc((z + 1) * sizeof(struct huft))) == NULL) {
          if (h) huft_free(u[0]);
          return 3;
        }
        hufts += z + 1;
        *t = q + 1;
        *(t = &(q->v.t)) = (struct huft *)NULL;
        u[h] = ++q;
        if (h) {
          x[h] = i;
          r.b = (uch)l;
          r.e = (uch)(16 + j);
          r.v.t = q;
          j = i >> (w - l);
          u[h-1][j] = r;
        }
      }

      r.b = (uch)(k - w);
      if (p >= v + n)
        r.e = 99;
      else if (*p < s) {
        r.e = (uch)(*p < 256 ? 16 : 15);
        r.v.n = (ush)(*p);
        p++;
      } else {
        r.e = (uch)e[*p - s];
        r.v.n = d[*p++ - s];
      }

      f = 1 << (k - w);
      for (j = i >> w; j < z; j += f)
        q[j] = r;

      for (j = 1 << (k - 1); i & j; j >>= 1)
        i ^= j;
      i ^= j;

      while ((i & ((1 << w) - 1)) != x[h]) {
        h--;
        w -= l;
      }
    }
  }

  return y != 0 && g != 1;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * huft_free — unchanged from original.
 * ═══════════════════════════════════════════════════════════════════════════ */
static int
huft_free(struct huft *t)
{
  register struct huft *p, *q;
  p = t;
  while (p != (struct huft *)NULL) {
    q = (--p)->v.t;
    free(p);
    p = q;
  }
  return 0;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * inflate_codes — hot inner loop, fully CXU-accelerated.
 * ═══════════════════════════════════════════════════════════════════════════ */
static int
inflate_codes(struct huft *tl, struct huft *td, int bl, int bd)
{
  register unsigned e;
  unsigned n, d;
  unsigned w;
  struct huft *t;
  BS_DECL();   /* uint32_t _bs */

  /* Load globals into local packed state and window position. */
  BS_INIT();
  w = wp;

  for (;;) {

    /* ── Decode one literal/length symbol ──────────────────────────────── */
    NEEDBITS_HW((unsigned)bl);
    t = tl + HUFT_IDX(bl);
    e = t->e;

    if (e > 16) {
      do {
        if (e == 99) { BS_SAVE(); return 1; }
        DUMPBITS_HW(t->b);
        e -= 16;
        NEEDBITS_HW(e);
        t = t->v.t + HUFT_IDX(e);
      } while ((e = t->e) > 16);
    }
    DUMPBITS_HW(t->b);

    if (e == 16) {
      /* ── Literal byte ─────────────────────────────────────────────── */
      slide[w++] = (uch)t->v.n;
      Tracevv((stderr, "%c", slide[w-1]));
      if (w == WSIZE) {
        flush_output(w);
        w = 0;
      }

    } else {
      /* ── Length/distance pair or EOB ──────────────────────────────── */
      if (e == 15)
        break;   /* end of block */

      /* Get length. */
      NEEDBITS_HW(e);
      n = t->v.n + PEEKBITS_HW(e);
      DUMPBITS_HW(e);

      /* Decode distance. */
      NEEDBITS_HW((unsigned)bd);
      t = td + HUFT_IDX(bd);
      e = t->e;

      if (e > 16) {
        do {
          if (e == 99) { BS_SAVE(); return 1; }
          DUMPBITS_HW(t->b);
          e -= 16;
          NEEDBITS_HW(e);
          t = t->v.t + HUFT_IDX(e);
        } while ((e = t->e) > 16);
      }
      DUMPBITS_HW(t->b);

      NEEDBITS_HW(e);
      d = w - t->v.n - PEEKBITS_HW(e);
      DUMPBITS_HW(e);
      Tracevv((stderr, "\\[%d,%d]", w-d, n));

      /* ── Sliding-window copy ────────────────────────────────────────── */
      do {
        /* Wrap both pointers into [0, WSIZE). */
        d = cfu_slide_wrap(d, 0);

        /* How many bytes can we copy without wrapping either pointer? */
        e = WSIZE - (d > w ? d : w);
        if (e > n) e = n;
        n -= e;

#ifndef DEBUG
        if (e <= (d < w ? w - d : d - w)) {
          memcpy(slide + w, slide + d, e);
          w += e;
          d += e;
        } else
#endif
        {
          do {
            slide[w++] = slide[d++];
            Tracevv((stderr, "%c", slide[w-1]));
          } while (--e);
        }

        if (w == WSIZE) {
          flush_output(w);
          w = 0;
        }
      } while (n);
    }
  }

  /* Flush state back to globals. */
  wp = w;
  BS_SAVE();
  return 0;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * inflate_stored — type 0 (uncompressed) block, CXU-accelerated.
 * ═══════════════════════════════════════════════════════════════════════════ */
static int
inflate_stored(void)
{
  unsigned n;
  unsigned w;
  BS_DECL();

  BS_INIT();
  w = wp;

  /* Align to byte boundary — dump the sub-byte leftover. */
  {
    unsigned leftover = cfu_bk(_bs) & 7u;
    DUMPBITS_HW(leftover);
  }

  /* Read 16-bit length and its one's-complement check. */
  NEEDBITS_HW(16);
  n = PEEKBITS_HW(16);
  DUMPBITS_HW(16);

  NEEDBITS_HW(16);
  if (n != (unsigned)(PEEKBITS_HW(16) ^ 0xffffu)) {
    BS_SAVE();
    return 1;   /* error in compressed data */
  }
  DUMPBITS_HW(16);

  /* Copy n raw bytes. */
  while (n--) {
    NEEDBITS_HW(8);
    slide[w++] = (uch)PEEKBITS_HW(8);
    if (w == WSIZE) {
      flush_output(w);
      w = 0;
    }
    DUMPBITS_HW(8);
  }

  wp = w;
  BS_SAVE();
  return 0;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * inflate_fixed — type 1 (fixed Huffman) block.
 * Table setup is software-only; inflate_codes() does the hot work via CXU.
 * ═══════════════════════════════════════════════════════════════════════════ */
static int
inflate_fixed(void)
{
  int i;
  struct huft *tl, *td;
  int bl, bd;
  unsigned l[288];

  /* Build fixed literal/length table. */
  for (i = 0;   i < 144; i++) l[i] = 8;
  for (;         i < 256; i++) l[i] = 9;
  for (;         i < 280; i++) l[i] = 7;
  for (;         i < 288; i++) l[i] = 8;
  bl = 7;
  if ((i = huft_build(l, 288, 257, cplens, cplext, &tl, &bl)) != 0)
    return i;

  /* Build fixed distance table. */
  for (i = 0; i < 30; i++) l[i] = 5;
  bd = 5;
  if ((i = huft_build(l, 30, 0, cpdist, cpdext, &td, &bd)) > 1) {
    huft_free(tl);
    return i;
  }

  /* Decode the block. */
  if (inflate_codes(tl, td, bl, bd))
    return 1;

  huft_free(tl);
  huft_free(td);
  return 0;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * inflate_dynamic — type 2 (dynamic Huffman) block.
 * Header parsing uses CXU; inflate_codes() handles the payload.
 * ═══════════════════════════════════════════════════════════════════════════ */
static int
inflate_dynamic(void)
{
  int i;
  unsigned j, l, m, n, w;
  struct huft *tl, *td;
  int bl, bd;
  unsigned nb, nl, nd;

#ifdef PKZIP_BUG_WORKAROUND
  unsigned ll[288 + 32];
#else
  unsigned ll[286 + 30];
#endif

  BS_DECL();
  BS_INIT();
  w = wp;

  /* ── Read table lengths ──────────────────────────────────────────────── */
  NEEDBITS_HW(5);
  nl = 257 + PEEKBITS_HW(5);   /* number of literal/length codes */
  DUMPBITS_HW(5);

  NEEDBITS_HW(5);
  nd = 1 + PEEKBITS_HW(5);     /* number of distance codes */
  DUMPBITS_HW(5);

  NEEDBITS_HW(4);
  nb = 4 + PEEKBITS_HW(4);     /* number of bit-length codes */
  DUMPBITS_HW(4);

#ifdef PKZIP_BUG_WORKAROUND
  if (nl > 288 || nd > 32)
#else
  if (nl > 286 || nd > 30)
#endif
  {
    BS_SAVE();
    return 1;   /* bad lengths */
  }

  /* ── Read bit-length-code lengths (3 bits each) ──────────────────────── */
  for (j = 0; j < nb; j++) {
    NEEDBITS_HW(3);
    ll[border[j]] = PEEKBITS_HW(3);
    DUMPBITS_HW(3);
  }
  for (; j < 19; j++)
    ll[border[j]] = 0;

  /* ── Build decoding table for the code-length alphabet ──────────────── */
  /* Flush state before calling huft_build (it doesn't touch the bit stream,
   * but we need wp consistent for error paths). */
  wp = w;
  BS_SAVE();

  bl = 7;
  if ((i = huft_build(ll, 19, 19, NULL, NULL, &tl, &bl)) != 0) {
    if (i == 1) huft_free(tl);
    return i;
  }
  if (tl == NULL)
    return 2;

  /* Reload after the huft_build call. */
  BS_INIT();
  w = wp;

  /* ── Read literal/length and distance code lengths ───────────────────── */
  n = nl + nd;
  m = mask_bits[bl];
  i = l = 0;

  while ((unsigned)i < n) {
    struct huft *td_tmp;

    NEEDBITS_HW((unsigned)bl);
    td_tmp = tl + HUFT_IDX(bl);
    j = td_tmp->b;
    DUMPBITS_HW(j);
    j = td_tmp->v.n;

    if (j < 16) {
      /* Literal code length 0..15. */
      ll[i++] = l = j;

    } else if (j == 16) {
      /* Repeat last length 3..6 times. */
      NEEDBITS_HW(2);
      j = 3 + PEEKBITS_HW(2);
      DUMPBITS_HW(2);
      if ((unsigned)i + j > n) { huft_free(tl); BS_SAVE(); return 1; }
      while (j--) ll[i++] = l;

    } else if (j == 17) {
      /* 3..10 zero-length codes. */
      NEEDBITS_HW(3);
      j = 3 + PEEKBITS_HW(3);
      DUMPBITS_HW(3);
      if ((unsigned)i + j > n) { huft_free(tl); BS_SAVE(); return 1; }
      while (j--) ll[i++] = 0;
      l = 0;

    } else {
      /* j == 18: 11..138 zero-length codes. */
      NEEDBITS_HW(7);
      j = 11 + PEEKBITS_HW(7);
      DUMPBITS_HW(7);
      if ((unsigned)i + j > n) { huft_free(tl); BS_SAVE(); return 1; }
      while (j--) ll[i++] = 0;
      l = 0;
    }
  }

  huft_free(tl);

  wp = w;
  BS_SAVE();   /* flush before huft_build calls */

  /* ── Build literal/length decoding table ─────────────────────────────── */
  bl = lbits;
  if ((i = huft_build(ll, nl, 257, cplens, cplext, &tl, &bl)) != 0) {
    if (i == 1) {
      Trace((stderr, " incomplete literal tree\n"));
      huft_free(tl);
    }
    return i;
  }

  /* ── Build distance decoding table ──────────────────────────────────── */
  bd = dbits;
  if ((i = huft_build(ll + nl, nd, 0, cpdist, cpdext, &td, &bd)) != 0) {
    if (i == 1) {
      Trace((stderr, " incomplete distance tree\n"));
#ifdef PKZIP_BUG_WORKAROUND
      i = 0;
    }
#else
      huft_free(td);
    }
    huft_free(tl);
    return i;
#endif
  }

  /* ── Decode the block payload (the hot path) ─────────────────────────── */
  {
    int err = inflate_codes(tl, td, bl, bd) ? 1 : 0;
    huft_free(tl);
    huft_free(td);
    return err;
  }
}

/* ═══════════════════════════════════════════════════════════════════════════
 * inflate_block — read block header, dispatch to stored/fixed/dynamic.
 * ═══════════════════════════════════════════════════════════════════════════ */
static int
inflate_block(int *e)
{
  unsigned t;
  BS_DECL();

  BS_INIT();

  /* Last-block flag. */
  NEEDBITS_HW(1);
  *e = (int)PEEKBITS_HW(1);
  DUMPBITS_HW(1);

  /* Block type (2 bits). */
  NEEDBITS_HW(2);
  t = PEEKBITS_HW(2);
  DUMPBITS_HW(2);

  BS_SAVE();

  switch (t) {
    case 0: return inflate_stored();
    case 1: return inflate_fixed();
    case 2: return inflate_dynamic();
    default: return 2;   /* bad block type */
  }
}

/* ═══════════════════════════════════════════════════════════════════════════
 * inflate — top-level entry point, unchanged in structure.
 * ═══════════════════════════════════════════════════════════════════════════ */
int
inflate(void)
{
  int e;
  int r;
  unsigned h;

  /* Initialise window, global bit-buffer. */
  wp = 0;
  bk = 0;
  bb = 0;

  h = 0;
  do {
    hufts = 0;
    if ((r = inflate_block(&e)) != 0)
      return r;
    if (hufts > h)
      h = hufts;
  } while (!e);

  /* Undo lookahead: align back to a byte boundary.
   * The next read will be byte-aligned, so discard any partial-byte bits. */
  while (bk >= 8) {
    bk -= 8;
    inptr--;
  }

  flush_output(wp);

  Trace((stderr, "<%u> ", h));
  return 0;
}
