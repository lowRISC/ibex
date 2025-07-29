/*
 *
 * Copyleft 2025 ISOLDE
 *
 */

#include <bsp/spm.h>

#include "simple_system_common.h"
#include "simple_system_regs.h"
#include "tinyprintf.h"

//#define SPM_VERBOSE 1

static uint32_t make_spm_address(uint32_t addr) {
  // Decode
  //  Extract bank select bits [5:2]
  uint32_t raw_bank = (addr & BANK_MASK) >> BANK_SHIFT;
  // adjust it to the available NUM_BANKS
  uint32_t bank_index = raw_bank % NUM_BANKS;

  // Extract offset within the bank (bits [31:6])
  uint32_t base_bank_offset = addr >> BANK_OFFSET_SHIFT;
  // Determine how many full rows were crossed(32 bits wide)
  uint32_t bank_row = (addr / WIDE_ADDR_ALIGNMENT) + (raw_bank / NUM_BANKS);
  //  Adjust the offset
  uint32_t bank_offset = base_bank_offset + bank_row;

  // Encode:
  uint32_t res = 0;
  res |= (bank_offset << BANK_OFFSET_SHIFT);  // bits [31:6]
  res |= (bank_index << BANK_SHIFT);          // bits [5:2]

  return res;
}

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
void to_spm(uint32_t addr, uint32_t *src, uint32_t elems) {
  if (addr & 0x3) {
    printf("Error: Address must be word-aligned for to_spm.\n");
    _Exit(0xbadc0de);
  }
#ifdef SPM_VERBOSE
  printf("*** >>\n");
#endif  
  volatile uint32_t *spm_addr;
  for (uint32_t i = 0; i < elems; ++i) {
    spm_addr = (uint32_t *)(SPM_NARROW_ADDR + make_spm_address(addr + 4 * i));
#ifdef SPM_VERBOSE
    printf("0x%x,",src[i]);
#endif
    *spm_addr = src[i];
  }
 #ifdef SPM_VERBOSE 
  printf("*** >>\n");
#endif
}

void to_spm_row(uint32_t row, uint32_t *src) {
  uint32_t addr = get_addr_start(row);
#ifdef SPM_VERBOSE
  printf("   *** >> row =%d, addr=0x%08x>>\n      ", row, addr);
#endif  
  volatile uint32_t *spm_addr;
  spm_addr = (uint32_t *)(addr + SPM_NARROW_ADDR);
  for (uint32_t i = 0; i < NUM_BANKS; ++i) {
#ifdef SPM_VERBOSE
    printf("0x%x,",src[i]);
#endif
    spm_addr[i] = src[i];
  }
 #ifdef SPM_VERBOSE 
  printf("   *** <<\n");
#endif
}
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
void from_spm(uint32_t addr, uint32_t *dst, uint32_t elems) {
  if (addr & 0x3) {
    printf("Error: Address must be word-aligned for from_spm.\n");
    _Exit(0xbadc0de);
  }

  volatile uint32_t *spm_addr;
  for (uint32_t i = 0; i < elems; ++i) {
    spm_addr = (uint32_t *)(SPM_NARROW_ADDR + make_spm_address(addr + 4 * i));
    dst[i] = *spm_addr;
  }
}


void from_spm_row(uint32_t *dst, uint32_t row) {
  uint32_t addr = get_addr_start(row);
#ifdef SPM_VERBOSE
  printf("   *** >> row =%d, addr=0x%08x>>\n      ", row, addr);
#endif  
  volatile uint32_t *spm_addr;
  spm_addr = (uint32_t *)(addr + SPM_NARROW_ADDR);
  for (uint32_t i = 0; i < NUM_BANKS; ++i) {
#ifdef SPM_VERBOSE
    printf("0x%x,",spm_addr[i]);
#endif
     dst[i]=spm_addr[i];
  }
 #ifdef SPM_VERBOSE 
  printf("   *** <<\n");
#endif
}

uint32_t get_addr_start(uint32_t row) {
  uint32_t bank_index = 0;
  uint32_t res = 0;
  res |= (row << BANK_OFFSET_SHIFT);  // bits [31:6]
  res |= (bank_index << BANK_SHIFT);  // bits [5:2]
  return res;
}

uint32_t get_addr_end(uint32_t row) {
  uint32_t bank_index = (NUM_BANKS - 1);
  uint32_t res = 0;
  res |= (row << BANK_OFFSET_SHIFT);  // bits [31:6]
  res |= (bank_index << BANK_SHIFT);  // bits [5:2]
  return res;
}


uint32_t spm_write(uint32_t spm_addr, uint32_t *src, uint32_t elems) {
  uint32_t src_offset = 0;
  uint32_t row = get_row(spm_addr);
  uint32_t last_row = row + elems / (NUM_BANKS - 1);
  uint32_t spm_next_addr = get_addr_start(last_row );
#ifdef SPM_VERBOSE
  printf("Copy to SPM at address 0x%08x, %d elems in %d rows\n", spm_addr, elems,last_row-row);
#endif  
  while (row < last_row) {
    to_spm_row(row, &src[src_offset]);
    row++;
    src_offset += NUM_BANKS - 1;  // jump to next  vector of 32 bits elements
  }

  //printf("Copied to SPM at address 0x%08x, %d rows\n", spm_addr, row-1);
#ifdef SPM_VERBOSE  
  printf("Next spm address 0x%08x \n", spm_next_addr);
#endif  
  return spm_next_addr;
}

uint32_t spm_read(uint32_t *dst, uint32_t spm_addr,  uint32_t elems) {
  uint32_t offset = 0;
  uint32_t row = get_row(spm_addr);
  uint32_t last_row = row + elems / (NUM_BANKS - 1);
  uint32_t spm_next_addr = get_addr_start(last_row );
#ifdef SPM_VERBOSE
  printf("Read from SPM at address 0x%08x, %d elems in %d rows\n", spm_addr, elems,last_row-row);
#endif  
  while (row < last_row) {
    from_spm_row(&dst[offset],row );
    row++;
    offset += NUM_BANKS - 1;  // jump to next  vector of 32 bits elements
  }

  //printf("Copied to SPM at address 0x%08x, %d rows\n", spm_addr, row-1);
 #ifdef SPM_VERBOSE 
  printf("Next spm address 0x%08x \n", spm_next_addr);
 #endif 
  return spm_next_addr;
}

