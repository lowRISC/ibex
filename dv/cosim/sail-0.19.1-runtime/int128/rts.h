#pragma once

#include<inttypes.h>
#include<stdlib.h>
#include<stdio.h>

#include"sail.h"

/*
 * This function should be called whenever a pattern match failure
 * occurs. Pattern match failures are always fatal.
 */
void sail_match_failure(const_sail_string msg);

/*
 * sail_assert implements the assert construct in Sail. If any
 * assertion fails we immediately exit the model.
 */
unit sail_assert(bool b, const_sail_string msg);

unit sail_exit(unit);

/*
 * sail_get_verbosity reads a 64-bit value that the C runtime allows you to set
 * on the command line.
 * The intention is that you can use individual bits to turn on/off different
 * pieces of debugging output.
 */
fbits sail_get_verbosity(const unit u);

/*
 * Put processor to sleep until an external device calls wakeup_request().
 */
unit sleep_request(const unit u);

/*
 * Stop processor sleeping.
 * (Typically called when a device generates an interrupt.)
 */
unit wakeup_request(const unit u);

/*
 * Test whether processor is sleeping.
 * (Typically used to disable execution of instructions.)
 */
bool sleeping(const unit u);

/* ***** Memory builtins ***** */

void write_mem(uint64_t, uint64_t);
uint64_t read_mem(uint64_t);

// These memory builtins are intended to match the semantics for the
// __ReadRAM and __WriteRAM functions in ASL.

bool write_ram(const sail_int addr_size,     // Either 32 or 64
	       const sail_int data_size_mpz, // Number of bytes
	       const lbits hex_ram,          // Currently unused
	       const lbits addr_bv,
	       const lbits data);

void read_ram(lbits *data,
	      const sail_int addr_size,
	      const sail_int data_size_mpz,
	      const lbits hex_ram,
	      const lbits addr_bv);

sbits fast_read_ram(const int64_t data_size,
		    const uint64_t addr_bv);

unit write_tag_bool(const fbits, const bool);
bool read_tag_bool(const fbits);

unit load_raw(fbits addr, const_sail_string file);

void load_image(char *);

/*
 * Functions for counting and limiting cycles
 */

// increment cycle count and test if over limit
bool cycle_limit_reached(const unit);

// increment cycle count and abort if over
unit cycle_count(const unit);

// read cycle count
sail_int get_cycle_count(const unit);

/*
 * Functions to get info from ELF files.
 */

sail_int elf_entry(const unit u);
sail_int elf_tohost(const unit u);

int process_arguments(int, char**);

/*
 * setup_rts and cleanup_rts are responsible for calling setup_library
 * and cleanup_library in sail.h.
 */
void setup_rts(void);
void cleanup_rts(void);

unit z__SetConfig(const_sail_string, sail_int);
unit z__ListConfig(const unit u);
