#pragma once
#ifndef CXU_HELPERS_H
#define CXU_HELPERS_H

#include "cfu.h"
#include "cxu_runtime.h"

/* ==========================================================================
   CXU helper wrappers
   ========================================================================== */
static inline unsigned cxu_bitrev(unsigned n)
{
  return (unsigned)cfu_op0(0, (uint32_t)n, 0u);
}

/* FN 0 — mask: returns (1 << n) - 1 */
static inline unsigned cxu_mask(unsigned n)
{
  return (unsigned)cfu_op2(0, (uint32_t)n, 0u);
}

/* FN 1 — huft_idx: returns (unsigned)(b & ((1 << bl) - 1))
   This is the dominant operation in inflate_codes(); every Huffman symbol
   decode performs exactly this before indexing the lookup table.           */
static inline unsigned cxu_huft_idx(ulg b, unsigned bl)
{
  return (unsigned)cfu_op3(0, (uint32_t)b, (uint32_t)bl);
}

/* FN 3 — copy_addr: fused back-reference address
   Returns (w - dist_base - extra_val) & 0x7FFF in bits [15:0].            */
static inline unsigned cxu_copy_addr(unsigned w, unsigned dist_base,
                                     unsigned extra_val)
{
  uint32_t rs1 = ((uint32_t)(w         & 0xFFFFu) << 16)
               |  (uint32_t)(dist_base  & 0xFFFFu);
  uint32_t result = (uint32_t)cfu_op4(0, rs1, (uint32_t)(extra_val & 0xFFFFu));
  return (unsigned)(result & 0x7FFFu);
}


#endif
