#ifndef CFU_INFLATE_H
#define CFU_INFLATE_H

#include <stdint.h>
#include "cfu.h"


static inline uint32_t cfu_pack(uint32_t bb, uint32_t bk)
{
    return cfu_op6_hw(0, bb, bk);
}

static inline uint32_t cfu_bb(uint32_t state)
{
    return cfu_op7_hw(0, state, 0);
}

static inline uint32_t cfu_bk(uint32_t state)
{
    return cfu_op7_hw(0, state, 1);
}

static inline uint32_t cfu_load_byte(uint32_t state, uint8_t byte)
{
    return cfu_op0_hw(0, state, (uint32_t)byte);
}

static inline uint32_t cfu_peek(uint32_t state, uint32_t n)
{
    return cfu_op1_hw(0, state, n);
}

static inline uint32_t cfu_dump(uint32_t state, uint32_t n)
{
    return cfu_op2_hw(0, state, n);
}

static inline uint32_t cfu_need_check(uint32_t state, uint32_t n)
{
    return cfu_op3_hw(0, state, n);
}

static inline uint32_t cfu_huft_idx(uint32_t raw_bb, uint32_t bl)
{
    return cfu_op4_hw(0, raw_bb, bl);
}

static inline uint32_t cfu_slide_wrap(uint32_t w, uint32_t inc)
{
    return cfu_op5_hw(0, w, inc);
}

#endif
