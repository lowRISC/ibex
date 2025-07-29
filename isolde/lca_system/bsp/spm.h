/*
 *
 * Copyleft 2025 ISOLDE
 *
 */

#ifndef __SCP_H__
#define __SCP_H__

#include <stdint.h>

#define WORD_ALIGN_MASK 0x3
#define BANK_MASK 0x3C  // Bits [5:2]
#define BANK_SHIFT 2
#define BANK_OFFSET_SHIFT 6  // Bits [31:6]

static const uint32_t NUM_BANKS = 9;
static const uint32_t BANK_DATA_WIDTH = 32;
static const uint32_t WIDE_ADDR_ALIGNMENT =
    (NUM_BANKS - 1) * (BANK_DATA_WIDTH / 4);

/**
 *  Copies data from a source array to SPM at a specified address
 *  The function checks for these conditions and exits with an error message if
 * they are not met Parameters:
 *   - addr is the starting address in SPM where data will be copied
 *     - must be word-aligned (i.e., divisible by 4)
 *     - must be within the range [0, SPM_NARROW_SIZE)
 *   - src is the source array to copy from
 *   - elems is the number of elements to copy, each element is 4 bytes wide
 */
void to_spm(uint32_t addr, uint32_t *src, uint32_t elems);
void to_spm_row(uint32_t row, uint32_t *src);
uint32_t spm_write(uint32_t spm_addr, uint32_t *src, uint32_t elems);

/**
 * Copies data from SPM to a destination array
 *  The function checks for these conditions and exits with an error message if
 * they are not met Parameters:
 *   - addr is the starting address in SPM from where data will be copied
 *     - must be word-aligned (i.e., divisible by 4)
 *     - must be within the range [0, SPM_NARROW_SIZE)
 *   - dst is the destination array to copy to
 *   - elems is the number of elements to copy, each element is 4 bytes wide
 */
void from_spm(uint32_t addr, uint32_t *dst, uint32_t elems);
void from_spm_row(uint32_t* dst, uint32_t row) ;
uint32_t spm_read(uint32_t *dst, uint32_t spm_addr,  uint32_t elems);

uint32_t get_addr_start(uint32_t row);
uint32_t get_addr_end(uint32_t row);
inline uint32_t get_row(uint32_t addr) { return (addr >> BANK_OFFSET_SHIFT); }
#endif