#pragma once

#ifndef CXU_RUNTIME_H
#define CXU_RUNTIME_H

#include <stdint.h>

#define STATE_AND_INDEX_CSR 0xBC0

// CSR read/write macros
#define cxu_csr_read(csr)                                                          \
  ({                                                                           \
    uint32_t __val;                                                            \
    asm volatile("csrr %0, %1" : "=r"(__val) : "i"(csr));                      \
    __val;                                                                     \
  })

#define cxu_csr_write(csr, val)                                                    \
  ({ asm volatile("csrw %0, %1" ::"i"(csr), "r"(val)); })

/**
 * Set the CSR to zero
 */
static inline void cxu_csr_clear(void) { cxu_csr_write(STATE_AND_INDEX_CSR, 0); }

/**
 * Set the version and selector/index fields
 * @param selector: 32-bit value for mcx_selector
 */
static inline void cxu_csr_set_selector(uint32_t selector) {
  cxu_csr_write(STATE_AND_INDEX_CSR, selector);
}

/**
 * Set all 32 bits of the CSR to a custom value
 * @param value: 32-bit value to write
 */
static inline void cxu_csr_set_raw(uint32_t value) { cxu_csr_write(STATE_AND_INDEX_CSR, value); }

#endif
