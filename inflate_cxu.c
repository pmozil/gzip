/* Inflate deflated data

   Copyright (C) 1997-1999, 2002, 2006, 2009-2025 Free Software Foundation,
   Inc.

   (Standard GNU header truncated for brevity)
*/

#include <config.h>
#include <stdlib.h>

#include "tailor.h"
#include "gzip.h"
#include "cxu_opt_funcs.h"

#define slide window

struct huft {
  uch e;                /* number of extra bits or operation */
  uch b;                /* number of bits in this code or subcode */
  union {
    ush n;              /* literal, length base, or distance base */
    struct huft *t;     /* pointer to next level of table */
  } v;
};

/* Function prototypes */
static int huft_free (struct huft *);

static bool fresh;
#define wp outcnt
#define flush_output(w) (fresh = false, wp = (w), flush_window ())

/* Tables for deflate from PKZIP's appnote.txt. */
static unsigned border[] = {    /* Order of the bit length code lengths */
        16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15};
static ush cplens[] = {         /* Copy lengths for literal codes 257..285 */
        3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
        35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258, 0, 0};
static ush cplext[] = {         /* Extra bits for literal codes 257..285 */
        0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
        3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 99, 99}; /* 99==invalid */
static ush cpdist[] = {         /* Copy offsets for distance codes 0..29 */
        1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
        257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
        8193, 12289, 16385, 24577};
static ush cpdext[] = {         /* Extra bits for distance codes */
        0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
        7, 7, 8, 8, 9, 9, 10, 10, 11, 11,
        12, 12, 13, 13};

static ulg bb;                         /* bit buffer */
static unsigned bk;                    /* bits in bit buffer */

#define GETBYTE() (inptr < insize ? inbuf[inptr++] : (wp = w, fill_inbuf(0)))

#define NEXTBYTE()  (uch)GETBYTE()
#define NEEDBITS(n) {while(k<(n)){b|=((ulg)NEXTBYTE())<<k;k+=8;}}
#define DUMPBITS(n) {b>>=(n);k-=(n);}

static int lbits = 9;   /* bits in base literal/length lookup table */
static int dbits = 6;   /* bits in base distance lookup table */

#define BMAX 16         /* maximum bit length of any code (16 for explode) */
#define N_MAX 288       /* maximum number of codes in any set */

static unsigned hufts;  /* track memory usage */

static int huft_build(
unsigned *b,            /* code lengths in bits (all assumed <= BMAX) */
unsigned n,             /* number of codes (assumed <= N_MAX) */
unsigned s,             /* number of simple-valued codes (0..s-1) */
ush *d,                 /* list of base values for non-simple codes */
ush *e,                 /* list of extra bits for non-simple codes */
struct huft **t,        /* result: starting table */
int *m                  /* maximum lookup bits, returns actual */
           )
{
  unsigned a;
  unsigned c[BMAX+1];
  unsigned f;
  int g;
  int h;
  register unsigned i;
  register unsigned j;
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
  p = b;  i = n;
  do {
    c[*p]++;
    p++;
  } while (--i);
  if (c[0] == n) {
    q = (struct huft *) malloc (3 * sizeof *q);
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

  for (y = 1 << j; j < i; j++, y <<= 1) if ((y -= c[j]) < 0) return 2;
  if ((y -= c[i]) < 0) return 2;
  c[i] += y;

  x[1] = j = 0;
  p = c + 1;  xp = x + 2;
  while (--i) *xp++ = (j += *p++);

  p = b;  i = 0;
  do {
    if ((j = *p++) != 0) v[x[j]++] = i;
  } while (++i < n);
  n = x[g];

  x[0] = i = 0;
  p = v;
  h = -1;
  w = -l;
  u[0] = (struct huft *)NULL;
  q = (struct huft *)NULL;
  z = 0;

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

        if ((q = (struct huft *)malloc((z + 1)*sizeof(struct huft))) == (struct huft *)NULL) {
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
      if (p >= v + n) r.e = 99;
      else if (*p < s) {
        r.e = (uch)(*p < 256 ? 16 : 15);
        r.v.n = (ush)(*p);
        p++;
      }
      else {
        r.e = (uch)e[*p - s];
        r.v.n = d[*p++ - s];
      }

      f = 1 << (k - w);
      for (j = i >> w; j < z; j += f) q[j] = r;
      for (j = 1 << (k - 1); i & j; j >>= 1) i ^= j;
      i ^= j;

      while ((i & ((1 << w) - 1)) != x[h]) {
        h--; w -= l;
      }
    }
  }
  return y != 0 && g != 1;
}

static int huft_free(struct huft *t)
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

static int inflate_codes(struct huft *tl, struct huft *td, int bl, int bd)
{
  register unsigned e;  /* table entry flag/number of extra bits */
  unsigned n, d;        /* length and index for copy */
  unsigned w;           /* current window position */
  struct huft *t;       /* pointer to table entry */
  unsigned ml, md;      /* masks for bl and bd bits */
  register ulg b;       /* bit buffer */
  register unsigned k;  /* number of bits in bit buffer */

  b = bb; k = bk; w = wp;

  /* Hardcoded CXU instructions removing variable mask_bits[] array reads */
  ml = cxu_mask(bl);
  md = cxu_mask(bd);

  for (;;) {
    NEEDBITS((unsigned)bl)
    if ((e = (t = tl + ((unsigned)b & ml))->e) > 16)
      do {
        if (e == 99) return 1;
        DUMPBITS(t->b)
        e -= 16;
        NEEDBITS(e)
      } while ((e = (t = t->v.t + cxu_huft_idx(b, e))->e) > 16);
    DUMPBITS(t->b)

    if (e == 16) {
      slide[w++] = (uch)t->v.n;
      if (w == WSIZE) {
        flush_output(w);
        w = 0;
      }
    } else {
      if (e == 15) break;

      NEEDBITS(e)
      /* Hardware handles resolving variable extra length bits */
      n = t->v.n + cxu_huft_idx(b, e);
      DUMPBITS(e);

      NEEDBITS((unsigned)bd)
      if ((e = (t = td + ((unsigned)b & md))->e) > 16)
        do {
          if (e == 99) return 1;
          DUMPBITS(t->b)
          e -= 16;
          NEEDBITS(e)
        } while ((e = (t = t->v.t + cxu_huft_idx(b, e))->e) > 16);
      DUMPBITS(t->b)
      NEEDBITS(e)

      /* Pure C arithmetic for exact bounds matching - CXU accelerates extra bits ONLY */
      d = w - t->v.n - cxu_huft_idx(b, e);
      DUMPBITS(e)

      if (fresh && w <= d) return 1;

      do {
        n -= (e = (e = WSIZE - ((d &= WSIZE-1) > w ? d : w)) > n ? n : e);
        if (e <= (d < w ? w - d : d - w)) {
          memcpy(slide + w, slide + d, e);
          w += e;
          d += e;
        } else {
          do { slide[w++] = slide[d++]; } while (--e);
        }
        if (w == WSIZE) {
          flush_output(w);
          w = 0;
        }
      } while (n);
    }
  }

  wp = w; bb = b; bk = k;
  return 0;
}

static int inflate_stored(void)
{
  unsigned n;
  unsigned w;
  register ulg b;
  register unsigned k;

  b = bb; k = bk; w = wp;

  n = k & 7;
  DUMPBITS(n);

  NEEDBITS(16)
  n = ((unsigned)b & 0xffff);
  DUMPBITS(16)
  NEEDBITS(16)
  if (n != (unsigned)((~b) & 0xffff)) return 1;
  DUMPBITS(16)

  while (n--) {
    NEEDBITS(8)
    slide[w++] = (uch)b;
    if (w == WSIZE) {
      flush_output(w); w = 0;
    }
    DUMPBITS(8)
  }

  wp = w; bb = b; bk = k;
  return 0;
}

static int inflate_fixed(void)
{
  int i;
  struct huft *tl;
  struct huft *td;
  int bl;
  int bd;
  unsigned l[288];

  for (i = 0; i < 144; i++) l[i] = 8;
  for (; i < 256; i++) l[i] = 9;
  for (; i < 280; i++) l[i] = 7;
  for (; i < 288; i++) l[i] = 8;
  bl = 7;
  if ((i = huft_build(l, 288, 257, cplens, cplext, &tl, &bl)) != 0) return i;

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

static int inflate_dynamic(void)
{
  int i;
  unsigned j;
  unsigned l;
  unsigned m;
  unsigned n;
  unsigned w;
  struct huft *tl;
  struct huft *td;
  int bl;
  int bd;
  unsigned nb;
  unsigned nl;
  unsigned nd;
#ifdef PKZIP_BUG_WORKAROUND
  unsigned ll[288+32];
#else
  unsigned ll[286+30];
#endif
  register ulg b;
  register unsigned k;

  b = bb; k = bk; w = wp;

  /* Use constant masks internally for single-cycle RISC-V ANDing where applicable */
  NEEDBITS(5)
  nl = 257 + ((unsigned)b & 0x1f);
  DUMPBITS(5)
  NEEDBITS(5)
  nd = 1 + ((unsigned)b & 0x1f);
  DUMPBITS(5)
  NEEDBITS(4)
  nb = 4 + ((unsigned)b & 0xf);
  DUMPBITS(4)

#ifdef PKZIP_BUG_WORKAROUND
  if (nl > 288 || nd > 32)
#else
  if (nl > 286 || nd > 30)
#endif
    return 1;

  for (j = 0; j < nb; j++) {
    NEEDBITS(3)
    ll[border[j]] = ((unsigned)b & 7);
    DUMPBITS(3)
  }
  for (; j < 19; j++) ll[border[j]] = 0;

  bl = 7;
  if ((i = huft_build(ll, 19, 19, NULL, NULL, &tl, &bl)) != 0) {
    if (i == 1) huft_free(tl);
    return i;
  }
  if (tl == NULL) return 2;

  n = nl + nd;
  m = cxu_mask(bl);

  i = l = 0;
  while ((unsigned)i < n) {
    NEEDBITS((unsigned)bl)
    j = (td = tl + ((unsigned)b & m))->b;
    DUMPBITS(j)
    if (td->e == 99) {
        huft_free (tl);
        return 2;
    }
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
    if (i == 1) huft_free(tl);
    return i;
  }
  bd = dbits;
  if ((i = huft_build(ll + nl, nd, 0, cpdist, cpdext, &td, &bd)) != 0) {
    if (i == 1) huft_free(td);
    huft_free(tl);
    return i;
  }

  {
    int err = inflate_codes(tl, td, bl, bd) ? 1 : 0;
    huft_free(tl);
    huft_free(td);
    return err;
  }
}

static int inflate_block(int *e)
{
  unsigned t;
  unsigned w;
  register ulg b;
  register unsigned k;

  b = bb; k = bk; w = wp;

  NEEDBITS(1)
  *e = (int)b & 1;
  DUMPBITS(1)

  NEEDBITS(2)
  t = (unsigned)b & 3;
  DUMPBITS(2)

  bb = b; bk = k;

  if (t == 2) return inflate_dynamic();
  if (t == 0) return inflate_stored();
  if (t == 1) return inflate_fixed();
  return 2;
}

int gzip_inflate ()
{
  int e;
  int r;
  unsigned h;

  wp = 0; bk = 0; bb = 0;
  fresh = true;

  h = 0;
  do {
    hufts = 0;
    if ((r = inflate_block(&e)) != 0) return r;
    if (hufts > h) h = hufts;
  } while (!e);

  while (bk >= 8) {
    bk -= 8;
    inptr--;
  }

  flush_output(wp);
  return 0;
}
