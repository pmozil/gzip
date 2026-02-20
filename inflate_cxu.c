/* Inflate deflated data — CXU-accelerated version

   Copyright (C) 1997-1999, 2002, 2006, 2009-2026 Free Software Foundation,
   Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* Not copyrighted 1992 by Mark Adler
   version c10p1, 10 January 1993 */

/* You can do whatever you like with this source file, though I would
   prefer that if you modify it and redistribute it that you include
   comments to that effect with your name and the date.  Thank you.
   [The history has been moved to the file ChangeLog.]
 */

#include <config.h>
#include <stdlib.h>

#include "cfu.h"
#include "cxu_runtime.h"
#include "tailor.h"
#include "gzip.h"
#define slide window

/* ==========================================================================
   CXU helper wrappers
   ========================================================================== */

/* FN 0 — mask: returns (1 << n) - 1 */
static inline unsigned cxu_mask(unsigned n)
{
  return (unsigned)cfu_op0(0, (uint32_t)n, 0u);
}

/* FN 1 — huft_idx: returns (unsigned)(b & ((1 << bl) - 1))
   This is the dominant operation in inflate_codes(); every Huffman symbol
   decode performs exactly this before indexing the lookup table.           */
static inline unsigned cxu_huft_idx(ulg b, unsigned bl)
{
  return (unsigned)cfu_op1(0, (uint32_t)b, (uint32_t)bl);
}

/* FN 3 — copy_addr: fused back-reference address
   Returns (w - dist_base - extra_val) & 0x7FFF in bits [15:0].            */
static inline unsigned cxu_copy_addr(unsigned w, unsigned dist_base,
                                     unsigned extra_val)
{
  uint32_t rs1 = ((uint32_t)(w         & 0xFFFFu) << 16)
               |  (uint32_t)(dist_base  & 0xFFFFu);
  uint32_t result = (uint32_t)cfu_op3(0, rs1, (uint32_t)(extra_val & 0xFFFFu));
  return (unsigned)(result & 0x7FFFu);
}

/* ==========================================================================
   Data structures — unchanged from original
   ========================================================================== */

struct huft {
  uch e;          /* extra bits / operation code */
  uch b;          /* bits in this code or subcode */
  union {
    ush n;        /* literal, length base, or distance base */
    struct huft *t;
  } v;
};

static int huft_free(struct huft *);

static bool fresh;
#define wp outcnt
#define flush_output(w) (fresh = false, wp = (w), flush_window())

/* Tables from PKZIP appnote.txt */
static unsigned border[] = {
  16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15
};
static ush cplens[] = {
  3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
  35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258, 0, 0
};
static ush cplext[] = {
  0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
  3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 99, 99
};
static ush cpdist[] = {
  1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
  257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
  8193, 12289, 16385, 24577
};
static ush cpdext[] = {
  0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
  7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13
};

static ulg      bb;        /* global bit buffer      */
static unsigned bk;        /* bits in bit buffer     */

static ush mask_bits[] = {
  0x0000,
  0x0001, 0x0003, 0x0007, 0x000f, 0x001f, 0x003f, 0x007f, 0x00ff,
  0x01ff, 0x03ff, 0x07ff, 0x0fff, 0x1fff, 0x3fff, 0x7fff, 0xffff
};

#define GETBYTE()   (inptr < insize ? inbuf[inptr++] : (wp = w, fill_inbuf(0)))
#define NEXTBYTE()  (uch)GETBYTE()
#define NEEDBITS(n) {while(k<(n)){b|=((ulg)NEXTBYTE())<<k;k+=8;}}
#define DUMPBITS(n) {b>>=(n);k-=(n);}

static int lbits = 9;
static int dbits = 6;

#define BMAX  16
#define N_MAX 288

static unsigned hufts;

static int
huft_build(unsigned *b, unsigned n, unsigned s,
           ush *d, ush *e, struct huft **t, int *m)
{
  unsigned a;
  unsigned c[BMAX+1];
  unsigned f;
  int      g;
  int      h;
  register unsigned  i;
  register unsigned  j;
  register int       k;
  int                l;
  register unsigned *p;
  register struct huft *q;
  struct huft  r;
  struct huft *u[BMAX];
  unsigned     v[N_MAX];
  register int w;
  unsigned     x[BMAX+1];
  unsigned    *xp;
  int          y;
  unsigned     z;

  /* Count bit lengths */
  memzero(c, sizeof(c));
  p = b; i = n;
  do {
#ifdef DEBUG
    if (1 < verbose && *p) {
      if (' ' <= n-i && n-i <= '~')
        fprintf(stderr, "%c %u\n", (char)(n-i), *p);
      else
        fprintf(stderr, "0x%x %u\n", n-i, *p);
    }
#endif
    c[*p]++;
    p++;
  } while (--i);

  if (c[0] == n) {
    q = (struct huft *)malloc(3 * sizeof *q);
    if (!q) return 3;
    hufts += 3;
    q[0].v.t = NULL;
    q[1].e = 99; q[1].b = 1;
    q[2].e = 99; q[2].b = 1;
    *t = q + 1;
    *m = 1;
    return 0;
  }

  /* Find min/max code lengths */
  l = *m;
  for (j = 1; j <= BMAX; j++) if (c[j]) break;
  k = j;
  if ((unsigned)l < j) l = j;
  for (i = BMAX; i; i--) if (c[i]) break;
  g = i;
  if ((unsigned)l > i) l = i;
  *m = l;

  /* Adjust last length count */
  for (y = 1 << j; j < i; j++, y <<= 1)
    if ((y -= c[j]) < 0) return 2;
  if ((y -= c[i]) < 0) return 2;
  c[i] += y;

  /* Starting offsets */
  x[1] = j = 0;
  p = c + 1; xp = x + 2;
  while (--i) *xp++ = (j += *p++);

  /* Values in order of bit length */
  p = b; i = 0;
  do {
    if ((j = *p++) != 0) v[x[j]++] = i;
  } while (++i < n);
  n = x[g];

  /* Generate Huffman codes and table entries */
  x[0] = i = 0;
  p = v;
  h = -1;
  w = -l;
  u[0] = NULL;
  q    = NULL;
  z    = 0;

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

        q = (struct huft *)malloc((z + 1) * sizeof(struct huft));
        if (!q) {
          if (h) huft_free(u[0]);
          return 3;
        }
        hufts += z + 1;
        *t = q + 1;
        *(t = &(q->v.t)) = NULL;
        u[h] = ++q;

        if (h) {
          x[h]  = i;
          r.b   = (uch)l;
          r.e   = (uch)(16 + j);
          r.v.t = q;
          j     = i >> (w - l);
          u[h-1][j] = r;
        }
      }

      r.b = (uch)(k - w);
      if (p >= v + n)
        r.e = 99;
      else if (*p < s) {
        r.e   = (uch)(*p < 256 ? 16 : 15);
        r.v.n = (ush)(*p);
        p++;
      } else {
        r.e   = (uch)e[*p - s];
        r.v.n = d[*p++ - s];
      }

      f = 1 << (k - w);
      for (j = i >> w; j < z; j += f)
        q[j] = r;

      for (j = 1 << (k - 1); i & j; j >>= 1)
        i ^= j;
      i ^= j;

      /* Back up over finished tables.
         Use FN 0 to compute the wrap mask (1<<w)-1 in hardware. */
      while ((i & cxu_mask((unsigned)w)) != x[h]) {
        h--;
        w -= l;
      }
    }
  }

  return y != 0 && g != 1;
}


static int
huft_free(struct huft *t)
{
  register struct huft *p, *q;
  p = t;
  while (p != NULL) {
    q = (--p)->v.t;
    free(p);
    p = q;
  }
  return 0;
}


static int
inflate_codes(struct huft *tl, struct huft *td, int bl, int bd)
{
  register unsigned e;
  unsigned    n, d;
  unsigned    w;
  struct huft *t;
  register ulg      b;
  register unsigned k;

  b = bb;
  k = bk;
  w = wp;

  for (;;)
  {
    NEEDBITS((unsigned)bl)
    t = tl + cxu_huft_idx(b, (unsigned)bl);
    e = t->e;

    if (e > 16)
      do {
        if (e == 99) return 1;
        DUMPBITS(t->b)
        e -= 16;
        NEEDBITS(e)
        /* FN 1 again for sub-table walk */
        t = t->v.t + cxu_huft_idx(b, e);
        e = t->e;
      } while (e > 16);

    DUMPBITS(t->b)

    if (e == 16)
    {
      /* literal */
      slide[w++] = (uch)t->v.n;
      Tracevv((stderr, "%c", slide[w-1]));
      if (w == WSIZE) { flush_output(w); w = 0; }
    }
    else
    {
      if (e == 15) break;   /* end of block */

      NEEDBITS(e)
      n = t->v.n + ((unsigned)b & cxu_mask(e));
      DUMPBITS(e)

      NEEDBITS((unsigned)bd)
      t = td + cxu_huft_idx(b, (unsigned)bd);
      e = t->e;

      if (e > 16)
        do {
          if (e == 99) return 1;
          DUMPBITS(t->b)
          e -= 16;
          NEEDBITS(e)
          t = t->v.t + cxu_huft_idx(b, e);
          e = t->e;
        } while (e > 16);

      DUMPBITS(t->b)
      NEEDBITS(e)

      {
        unsigned extra_val = (unsigned)b & cxu_mask(e);
        d = cxu_copy_addr(w, (unsigned)t->v.n, extra_val);
      }
      DUMPBITS(e)

      if (fresh && w <= d) return 1;
      Tracevv((stderr, "\\[%u,%u]", w - d, n));

      /* copy back-reference bytes */
      do {
        n -= (e = (e = WSIZE - ((d &= WSIZE-1) > w ? d : w)) > n ? n : e);
#ifndef DEBUG
        if (e <= (d < w ? w - d : d - w)) {
          memcpy(slide + w, slide + d, e);
          w += e;
          d += e;
        } else
#endif
          do {
            slide[w++] = slide[d++];
            Tracevv((stderr, "%c", slide[w-1]));
          } while (--e);
        if (w == WSIZE) { flush_output(w); w = 0; }
      } while (n);
    }
  }

  wp = w;
  bb = b;
  bk = k;
  return 0;
}


static int
inflate_stored(void)
{
  unsigned    n;
  unsigned    w;
  register ulg      b;
  register unsigned k;

  b = bb; k = bk; w = wp;

  n = k & 7;
  DUMPBITS(n)

  NEEDBITS(16)
  n = (unsigned)b & 0xffff;
  DUMPBITS(16)
  NEEDBITS(16)
  if (n != (unsigned)((~b) & 0xffff)) return 1;
  DUMPBITS(16)

  while (n--) {
    NEEDBITS(8)
    slide[w++] = (uch)b;
    if (w == WSIZE) { flush_output(w); w = 0; }
    DUMPBITS(8)
  }

  wp = w; bb = b; bk = k;
  return 0;
}


static int
inflate_fixed(void)
{
  int      i;
  struct huft *tl, *td;
  int      bl, bd;
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

  if (inflate_codes(tl, td, bl, bd)) return 1;

  huft_free(tl);
  huft_free(td);
  return 0;
}


static int
inflate_dynamic(void)
{
  int      i;
  unsigned j, l, m, n, w;
  struct huft *tl, *td;
  int      bl, bd;
  unsigned nb, nl, nd;
#ifdef PKZIP_BUG_WORKAROUND
  unsigned ll[288+32];
#else
  unsigned ll[286+30];
#endif
  register ulg      b;
  register unsigned k;

  b = bb; k = bk; w = wp;

  NEEDBITS(5)  nl = 257 + ((unsigned)b & 0x1f); DUMPBITS(5)
  NEEDBITS(5)  nd =   1 + ((unsigned)b & 0x1f); DUMPBITS(5)
  NEEDBITS(4)  nb =   4 + ((unsigned)b & 0x0f); DUMPBITS(4)
#ifdef PKZIP_BUG_WORKAROUND
  if (nl > 288 || nd > 32)
#else
  if (nl > 286 || nd > 30)
#endif
    return 1;

  for (j = 0; j < nb; j++) {
    NEEDBITS(3)
    ll[border[j]] = (unsigned)b & 7;
    DUMPBITS(3)
  }
  for (; j < 19; j++) ll[border[j]] = 0;

  bl = 7;
  if ((i = huft_build(ll, 19, 19, NULL, NULL, &tl, &bl)) != 0) {
    if (i == 1) huft_free(tl);
    return i;
  }
  if (tl == NULL) return 2;

  /* Read literal/distance code lengths.
     FN 1 accelerates the table index on every iteration.             */
  n = nl + nd;
  i = l = 0;
  while ((unsigned)i < n) {
    NEEDBITS((unsigned)bl)
    td = tl + cxu_huft_idx(b, (unsigned)bl);
    j  = td->b;
    DUMPBITS(j)
    if (td->e == 99) { huft_free(tl); return 2; }
    j = td->v.n;
    if (j < 16) {
      ll[i++] = l = j;
    } else if (j == 16) {
      NEEDBITS(2)
      j = 3 + ((unsigned)b & 3);
      DUMPBITS(2)
      if ((unsigned)i + j > n) return 1;
      while (j--) ll[i++] = l;
    } else if (j == 17) {
      NEEDBITS(3)
      j = 3 + ((unsigned)b & 7);
      DUMPBITS(3)
      if ((unsigned)i + j > n) return 1;
      while (j--) ll[i++] = 0;
      l = 0;
    } else {
      NEEDBITS(7)
      j = 11 + ((unsigned)b & 0x7f);
      DUMPBITS(7)
      if ((unsigned)i + j > n) return 1;
      while (j--) ll[i++] = 0;
      l = 0;
    }
  }

  huft_free(tl);
  bb = b; bk = k;

  bl = lbits;
  if ((i = huft_build(ll, nl, 257, cplens, cplext, &tl, &bl)) != 0) {
    if (i == 1) { Trace((stderr, " incomplete literal tree\n")); huft_free(tl); }
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

  {
    int err = inflate_codes(tl, td, bl, bd) ? 1 : 0;
    huft_free(tl);
    huft_free(td);
    return err;
  }
}


static int
inflate_block(int *e)
{
  unsigned    t;
  unsigned    w;
  register ulg      b;
  register unsigned k;

  b = bb; k = bk; w = wp;

  NEEDBITS(1) *e = (int)b & 1; DUMPBITS(1)
  NEEDBITS(2)  t = (unsigned)b & 3; DUMPBITS(2)

  bb = b; bk = k;

  if (t == 2) return inflate_dynamic();
  if (t == 0) return inflate_stored();
  if (t == 1) return inflate_fixed();
  return 2;
}


int
gzip_inflate(void)
{
  int      e;
  int      r;
  unsigned h;

  cxu_csr_clear();

  wp    = 0;
  bk    = 0;
  bb    = 0;
  fresh = true;

  h = 0;
  do {
    hufts = 0;
    if ((r = inflate_block(&e)) != 0) return r;
    if (hufts > h) h = hufts;
  } while (!e);

  while (bk >= 8) { bk -= 8; inptr--; }

  flush_output(wp);

  Trace((stderr, "<%u> ", h));
  return 0;
}
