/* inflate.c — Inflate deflated data, with CFU hardware bit-stream acceleration.
 *
 * Based on the original gzip inflate.c:
 *   Copyright (C) 1997-1999, 2002, 2006, 2009-2013 Free Software Foundation
 *   Original inflate algorithm: Mark Adler, "Not copyrighted 1992"
 *
 * CFU acceleration:
 *   Bit-buffer state is packed into a single uint32_t {bk[7:0], bb[23:0]}
 *   and passed by pointer through the call chain so there is never any
 *   ambiguity about which copy of bb/bk is live.  The globals bb/bk are
 *   only touched at the very top (inflate) and bottom (flush) of each
 *   public entry point.
 *
 *   huft_build / huft_free are pure software and completely unchanged.
 */

#include <config.h>
#include "tailor.h"
#include <stdlib.h>
#include "gzip.h"
#include "cxu_opt_funcs.h"

#define slide window

struct huft {
  uch e;
  uch b;
  union {
    ush n;
    struct huft *t;
  } v;
};

static int huft_free(struct huft *);

#define wp outcnt
#define flush_output(w) (wp = (w), flush_window())

static ulg      bb;
static unsigned bk;

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
    7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13};

static int lbits = 9;
static int dbits = 6;

static ush mask_bits[] = {
    0x0000,
    0x0001, 0x0003, 0x0007, 0x000f, 0x001f, 0x003f, 0x007f, 0x00ff,
    0x01ff, 0x03ff, 0x07ff, 0x0fff, 0x1fff, 0x3fff, 0x7fff, 0xffff
};

#define GETBYTE() \
    (inptr < insize ? inbuf[inptr++] : (wp = w, fill_inbuf(0)))

#ifdef CRYPT
  uch cc;
#  define NEXTBYTE() \
     (decrypt ? (cc = GETBYTE(), zdecode(cc), cc) : GETBYTE())
#else
#  define NEXTBYTE() (uch)GETBYTE()
#endif

typedef struct { uint32_t bs; unsigned w; } bstate_t;

static inline bstate_t bs_from_globals(void)
{
    bstate_t s;
    s.bs = cfu_pack((uint32_t)bb, (uint32_t)bk);
    s.w  = (unsigned)wp;
    return s;
}

static inline void bs_to_globals(bstate_t s)
{
    bb = (ulg)     cfu_bb(s.bs);
    bk = (unsigned)cfu_bk(s.bs);
    wp = s.w;
}

#define NEEDBITS(s, n) \
    while (cfu_need_check((s).bs, (unsigned)(n))) { \
        (s).bs = cfu_load_byte((s).bs, NEXTBYTE()); \
    }
#define DUMPBITS(s, n)   ((s).bs = cfu_dump((s).bs, (unsigned)(n)))
#define PEEKBITS(s, n)   cfu_peek((s).bs, (unsigned)(n))
#define HUFT_IDX(s, bl)  cfu_huft_idx(cfu_bb((s).bs), (unsigned)(bl))

#define BMAX 16
#define N_MAX 288
static unsigned hufts;

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
  do { c[*p]++; p++; } while (--i);

  if (c[0] == n) {
    q = (struct huft *) malloc(3 * sizeof *q);
    if (!q) return 3;
    hufts += 3;
    q[0].v.t = (struct huft *) NULL;
    q[1].e = 99; q[1].b = 1;
    q[2].e = 99; q[2].b = 1;
    *t = q + 1; *m = 1;
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
  do { if ((j = *p++) != 0) v[x[j]++] = i; } while (++i < n);
  n = x[g];

  x[0] = i = 0; p = v; h = -1; w = -l;
  u[0] = (struct huft *)NULL;
  q    = (struct huft *)NULL;
  z    = 0;

  for (; k <= g; k++) {
    a = c[k];
    while (a--) {
      while (k > w + l) {
        h++; w += l;
        z = (z = g - w) > (unsigned)l ? l : z;
        if ((f = 1 << (j = k - w)) > a + 1) {
          f -= a + 1; xp = c + k;
          if (j < z)
            while (++j < z) {
              if ((f <<= 1) <= *++xp) break;
              f -= *xp;
            }
        }
        z = 1 << j;
        if ((q = (struct huft *)malloc((z+1)*sizeof(struct huft))) == NULL) {
          if (h) huft_free(u[0]);
          return 3;
        }
        hufts += z + 1;
        *t = q + 1;
        *(t = &(q->v.t)) = (struct huft *)NULL;
        u[h] = ++q;
        if (h) {
          x[h] = i;
          r.b = (uch)l; r.e = (uch)(16 + j); r.v.t = q;
          j = i >> (w - l);
          u[h-1][j] = r;
        }
      }
      r.b = (uch)(k - w);
      if (p >= v + n) r.e = 99;
      else if (*p < s) {
        r.e = (uch)(*p < 256 ? 16 : 15);
        r.v.n = (ush)(*p); p++;
      } else {
        r.e = (uch)e[*p - s];
        r.v.n = d[*p++ - s];
      }
      f = 1 << (k - w);
      for (j = i >> w; j < z; j += f) q[j] = r;
      for (j = 1 << (k-1); i & j; j >>= 1) i ^= j;
      i ^= j;
      while ((i & ((1 << w) - 1)) != x[h]) { h--; w -= l; }
    }
  }
  return y != 0 && g != 1;
}

static int
huft_free(struct huft *t)
{
  register struct huft *p, *q;
  p = t;
  while (p != (struct huft *)NULL) { q = (--p)->v.t; free(p); p = q; }
  return 0;
}

static int
inflate_codes(bstate_t *sp, struct huft *tl, struct huft *td, int bl, int bd)
{
  register unsigned e;
  unsigned n, d;
  struct huft *t;
  bstate_t s = *sp;
  unsigned w = s.w;

  for (;;) {

    NEEDBITS(s, bl);
    t = tl + HUFT_IDX(s, bl);
    e = t->e;

    if (e > 16) {
      do {
        if (e == 99) { s.w = w; *sp = s; return 1; }
        DUMPBITS(s, t->b);
        e -= 16;
        NEEDBITS(s, e);
        t = t->v.t + HUFT_IDX(s, e);
      } while ((e = t->e) > 16);
    }
    DUMPBITS(s, t->b);

    if (e == 16) {
      slide[w++] = (uch)t->v.n;
      Tracevv((stderr, "%c", slide[w-1]));
      if (w == WSIZE) { flush_output(w); w = 0; }

    } else {
      if (e == 15) break;

      NEEDBITS(s, e);
      n = t->v.n + PEEKBITS(s, e);
      DUMPBITS(s, e);

      NEEDBITS(s, bd);
      t = td + HUFT_IDX(s, bd);
      e = t->e;
      if (e > 16) {
        do {
          if (e == 99) { s.w = w; *sp = s; return 1; }
          DUMPBITS(s, t->b);
          e -= 16;
          NEEDBITS(s, e);
          t = t->v.t + HUFT_IDX(s, e);
        } while ((e = t->e) > 16);
      }
      DUMPBITS(s, t->b);
      NEEDBITS(s, e);
      d = w - t->v.n - PEEKBITS(s, e);
      DUMPBITS(s, e);
      Tracevv((stderr, "\\[%d,%d]", w-d, n));

      do {
        d &= WSIZE - 1;
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
        if (w == WSIZE) { flush_output(w); w = 0; }
      } while (n);
    }
  }

  s.w = w;
  *sp = s;
  return 0;
}

static int
inflate_stored(bstate_t *sp)
{
  unsigned n;
  bstate_t s = *sp;
  unsigned w = s.w;

  {
    unsigned leftover = cfu_bk(s.bs) & 7u;
    DUMPBITS(s, leftover);
  }

  NEEDBITS(s, 16);
  n = PEEKBITS(s, 16);
  DUMPBITS(s, 16);

  NEEDBITS(s, 16);
  if (n != (unsigned)((~PEEKBITS(s, 16)) & 0xffffu)) {
    s.w = w; *sp = s;
    return 1;
  }
  DUMPBITS(s, 16);

  while (n--) {
    NEEDBITS(s, 8);
    slide[w++] = (uch)PEEKBITS(s, 8);
    if (w == WSIZE) { flush_output(w); w = 0; }
    DUMPBITS(s, 8);
  }

  s.w = w;
  *sp = s;
  return 0;
}

static int
inflate_fixed(bstate_t *sp)
{
  int i;
  struct huft *tl, *td;
  int bl, bd;
  unsigned l[288];

  for (i = 0;   i < 144; i++) l[i] = 8;
  for (;         i < 256; i++) l[i] = 9;
  for (;         i < 280; i++) l[i] = 7;
  for (;         i < 288; i++) l[i] = 8;
  bl = 7;
  if ((i = huft_build(l, 288, 257, cplens, cplext, &tl, &bl)) != 0)
    return i;

  for (i = 0; i < 30; i++) l[i] = 5;
  bd = 5;
  if ((i = huft_build(l, 30, 0, cpdist, cpdext, &td, &bd)) > 1) {
    huft_free(tl);
    return i;
  }

  i = inflate_codes(sp, tl, td, bl, bd) ? 1 : 0;

  huft_free(tl);
  huft_free(td);
  return i;
}

static int
inflate_dynamic(bstate_t *sp)
{
  int i;
  unsigned j, l, m, n;
  struct huft *tl, *td;
  int bl, bd;
  unsigned nb, nl, nd;
#ifdef PKZIP_BUG_WORKAROUND
  unsigned ll[288 + 32];
#else
  unsigned ll[286 + 30];
#endif
  bstate_t s = *sp;
  unsigned w = s.w;

  NEEDBITS(s, 5);
  nl = 257 + PEEKBITS(s, 5);
  DUMPBITS(s, 5);

  NEEDBITS(s, 5);
  nd = 1 + PEEKBITS(s, 5);
  DUMPBITS(s, 5);

  NEEDBITS(s, 4);
  nb = 4 + PEEKBITS(s, 4);
  DUMPBITS(s, 4);

#ifdef PKZIP_BUG_WORKAROUND
  if (nl > 288 || nd > 32)
#else
  if (nl > 286 || nd > 30)
#endif
    return 1;

  for (j = 0; j < nb; j++) {
    NEEDBITS(s, 3);
    ll[border[j]] = PEEKBITS(s, 3);
    DUMPBITS(s, 3);
  }
  for (; j < 19; j++)
    ll[border[j]] = 0;

  wp = w;

  bl = 7;
  if ((i = huft_build(ll, 19, 19, NULL, NULL, &tl, &bl)) != 0) {
    if (i == 1) huft_free(tl);
    return i;
  }
  if (tl == NULL) return 2;

  n = nl + nd;
  m = mask_bits[bl];
  (void)m;
  i = l = 0;

  while ((unsigned)i < n) {
    struct huft *td_tmp;

    NEEDBITS(s, bl);
    td_tmp = tl + HUFT_IDX(s, bl);
    j = td_tmp->b;
    DUMPBITS(s, j);
    j = td_tmp->v.n;

    if (j < 16) {
      ll[i++] = l = j;

    } else if (j == 16) {
      NEEDBITS(s, 2);
      j = 3 + PEEKBITS(s, 2);
      DUMPBITS(s, 2);
      if ((unsigned)i + j > n) { huft_free(tl); return 1; }
      while (j--) ll[i++] = l;

    } else if (j == 17) {
      NEEDBITS(s, 3);
      j = 3 + PEEKBITS(s, 3);
      DUMPBITS(s, 3);
      if ((unsigned)i + j > n) { huft_free(tl); return 1; }
      while (j--) ll[i++] = 0;
      l = 0;

    } else {
      NEEDBITS(s, 7);
      j = 11 + PEEKBITS(s, 7);
      DUMPBITS(s, 7);
      if ((unsigned)i + j > n) { huft_free(tl); return 1; }
      while (j--) ll[i++] = 0;
      l = 0;
    }
  }

  huft_free(tl);

  wp = w;

  bl = lbits;
  if ((i = huft_build(ll, nl, 257, cplens, cplext, &tl, &bl)) != 0) {
    if (i == 1) {
      Trace((stderr, " incomplete literal tree\n"));
      huft_free(tl);
    }
    return i;
  }

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

  s.w = w;
  {
    int err = inflate_codes(&s, tl, td, bl, bd) ? 1 : 0;
    huft_free(tl);
    huft_free(td);
    *sp = s;
    return err;
  }
}

static int
inflate_block(int *e)
{
  unsigned t;
  bstate_t s;
  int r;

  s = bs_from_globals();

  unsigned w = s.w;

  NEEDBITS(s, 1);
  *e = (int)PEEKBITS(s, 1);
  DUMPBITS(s, 1);

  NEEDBITS(s, 2);
  t = PEEKBITS(s, 2);
  DUMPBITS(s, 2);

  bs_to_globals(s);
  s = bs_from_globals();

  switch (t) {
    case 0: r = inflate_stored (&s); break;
    case 1: r = inflate_fixed  (&s); break;
    case 2: r = inflate_dynamic(&s); break;
    default: return 2;
  }

  bs_to_globals(s);
  return r;
}

int
gzip_inflate(void)
{
  int e;
  int r;
  unsigned h;

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

  while (bk >= 8) {
    bk -= 8;
    inptr--;
  }

  flush_output(wp);
  Trace((stderr, "<%u> ", h));
  return 0;
}
