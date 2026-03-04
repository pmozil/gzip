#pragma once
#ifndef CXU_HELPERS_H
#define CXU_HELPERS_H

#include "cfu.h"
#include "gzip.h"

/* FN 0 — bitrev: reverses 32 bits */
static inline unsigned cxu_bitrev(unsigned n)
{
  return (unsigned)cfu_op0(0, (uint32_t)n, 0u);
}

/* FN 2 — mask: returns (1 << n) - 1 */
static inline unsigned cxu_mask(unsigned n)
{
  return (unsigned)cfu_op2(0, (uint32_t)n, 0u);
}

/* FN 3 — huft_idx: returns (unsigned)(b & ((1 << bl) - 1))
   This merges the bitstream extraction and the bit masking in one step. */
static inline unsigned cxu_huft_idx(unsigned long b, unsigned bl)
{
  return (unsigned)cfu_op3(0, (uint32_t)b, (uint32_t)bl);
}

/* FN 4 — copy_addr: fused back-reference address
   Returns (w - dist_base - extra_val) & 0x7FFF in bits [15:0]. */
static inline unsigned cxu_copy_addr(unsigned w, unsigned dist_base,
                                     unsigned extra_val)
{
  uint32_t rs1 = ((uint32_t)(w & 0xFFFFu) << 16) | (uint32_t)(dist_base & 0xFFFFu);
  return (unsigned)cfu_op4(0, rs1, (uint32_t)(extra_val & 0xFFFFu));
}

#endif
