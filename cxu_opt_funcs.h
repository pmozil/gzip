#ifndef CFU_INFLATE_H
#define CFU_INFLATE_H

#include <stdint.h>
#include "cfu.h"

static inline uint32_t cfu_pack(uint32_t b, uint32_t k)
{ return cfu_op6_hw(0, b, k); }

static inline uint32_t cfu_bb(uint32_t s)
{ return cfu_op7_hw(0, s, 0); }

static inline uint32_t cfu_bk(uint32_t s)
{ return cfu_op7_hw(0, s, 1); }

static inline uint32_t cfu_load_byte(uint32_t s, uint8_t byte)
{ return cfu_op0_hw(0, s, (uint32_t)byte); }

static inline uint32_t cfu_peek(uint32_t s, uint32_t n)
{ return cfu_op1_hw(0, s, n); }

static inline uint32_t cfu_dump(uint32_t s, uint32_t n)
{ return cfu_op2_hw(0, s, n); }

static inline uint32_t cfu_need_check(uint32_t s, uint32_t n)
{ return cfu_op3_hw(0, s, n); }

static inline uint32_t cfu_huft_idx(uint32_t raw_bb, uint32_t bl)
{ return cfu_op4_hw(0, raw_bb, bl); }

#endif
