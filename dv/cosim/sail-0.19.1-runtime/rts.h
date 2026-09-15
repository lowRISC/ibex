/****************************************************************************/
/*     Sail                                                                 */
/*                                                                          */
/*  Sail and the Sail architecture models here, comprising all files and    */
/*  directories except the ASL-derived Sail code in the aarch64 directory,  */
/*  are subject to the BSD two-clause licence below.                        */
/*                                                                          */
/*  The ASL derived parts of the ARMv8.3 specification in                   */
/*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               */
/*                                                                          */
/*  Copyright (c) 2013-2021                                                 */
/*    Kathyrn Gray                                                          */
/*    Shaked Flur                                                           */
/*    Stephen Kell                                                          */
/*    Gabriel Kerneis                                                       */
/*    Robert Norton-Wright                                                  */
/*    Christopher Pulte                                                     */
/*    Peter Sewell                                                          */
/*    Alasdair Armstrong                                                    */
/*    Brian Campbell                                                        */
/*    Thomas Bauereiss                                                      */
/*    Anthony Fox                                                           */
/*    Jon French                                                            */
/*    Dominic Mulligan                                                      */
/*    Stephen Kell                                                          */
/*    Mark Wassell                                                          */
/*    Alastair Reid (Arm Ltd)                                               */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This work was partially supported by EPSRC grant EP/K008528/1 <a        */
/*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          */
/*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   */
/*  KTF funding, and donations from Arm.  This project has received         */
/*  funding from the European Research Council (ERC) under the European     */
/*  Union’s Horizon 2020 research and innovation programme (grant           */
/*  agreement No 789108, ELVER).                                            */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        */
/*  and FA8750-10-C-0237 ("CTSRD").                                         */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/****************************************************************************/

#ifndef SAIL_RTS_H
#define SAIL_RTS_H

#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>

#include "sail.h"
#include "sail_failure.h"

#ifdef __cplusplus
extern "C" {
#endif

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

bool write_ram(const mpz_t addr_size,     // Either 32 or 64
	       const mpz_t data_size_mpz, // Number of bytes
	       const lbits hex_ram,       // Currently unused
	       const lbits addr_bv,
	       const lbits data);

void read_ram(lbits *data,
	      const mpz_t addr_size,
	      const mpz_t data_size_mpz,
	      const lbits hex_ram,
	      const lbits addr_bv);

sbits fast_read_ram(const int64_t data_size,
		    const uint64_t addr_bv);

unit write_tag_bool(const fbits, const bool);
bool read_tag_bool(const fbits);

unit emulator_write_tag(const uint64_t addr_size, const sbits addr, const bool tag);
bool emulator_read_tag(const uint64_t addr_size, const sbits addr);

void platform_read_mem(lbits *data,
                       const int read_kind,
                       const uint64_t addr_size,
                       const sbits addr,
                       const mpz_t n);
unit platform_write_mem_ea(const int write_kind,
                           const uint64_t addr_size,
                           const sbits addr,
                           const mpz_t n);
bool platform_write_mem(const int write_kind,
                        const uint64_t addr_size,
                        const sbits addr,
                        const mpz_t n,
                        const lbits data);
bool platform_excl_res(const unit unit);
unit platform_barrier();

/* ***** New concurrency interface primitives ***** */

void emulator_read_mem(lbits *data,
                       const uint64_t addr_size,
                       const sbits addr,
                       const mpz_t n);

void emulator_read_mem_ifetch(lbits *data,
                              const uint64_t addr_size,
                              const sbits addr,
                              const mpz_t n);

void emulator_read_mem_exclusive(lbits *data,
                                 const uint64_t addr_size,
                                 const sbits addr,
                                 const mpz_t n);

bool emulator_write_mem(const uint64_t addr_size,
                        const sbits addr,
                        const mpz_t n,
                        const lbits data);

bool emulator_write_mem_exclusive(const uint64_t addr_size,
                                  const sbits addr,
                                  const mpz_t n,
                                  const lbits data);

unit load_raw(fbits addr, const_sail_string file);

void load_image(char *);

/* ***** Tracing ***** */

/*
 * Bind these functions in Sail to enable and disable tracing (see
 * lib/trace.sail):
 *
 * val "enable_tracing" : unit -> unit
 * val "disable_tracing" : unit -> unit
 * val "is_tracing" : unit -> bool
 *
 * Compile with sail -c -c_trace.
 */
unit enable_tracing(const unit);
unit disable_tracing(const unit);

bool is_tracing(const unit);

/*
 * Tracing is implemented by void trace_TYPE functions, each of which
 * takes the Sail value to print as the first argument, and prints it
 * directly to stderr with no linebreaks.
 *
 * For types that don't have printing function we have trace_unknown,
 * which simply prints '?'. trace_argsep, trace_argend, and
 * trace_retend are used for formatting function arguments. They won't
 * overlap with user defined types because the type names used for
 * TYPE are zencoded. trace_start(NAME) and trace_end() are called
 * before printing the function arguments and return value
 * respectively.
*/
void trace_sail_int(const sail_int);
void trace_bool(const bool);
void trace_unit(const unit);
void trace_sail_string(const_sail_string);
void trace_fbits(const fbits);
void trace_lbits(const lbits);

void trace_unknown(void);
void trace_argsep(void);
void trace_argend(void);
void trace_retend(void);
void trace_start(char *);
void trace_end(void);

/*
 * Functions for counting and limiting cycles
 */

// increment cycle count and test if over limit
bool cycle_limit_reached(const unit);

// increment cycle count and abort if over
unit cycle_count(const unit);

// read cycle count
void get_cycle_count(sail_int *rop, const unit);

/*
 * Functions to get info from ELF files.
 */

void elf_entry(sail_int *rop, const unit u);
void elf_tohost(sail_int *rop, const unit u);

int process_arguments(int, char**);

/*
 * setup_rts and cleanup_rts are responsible for calling setup_library
 * and cleanup_library in sail.h.
 */
void setup_rts(void);
void cleanup_rts(void);

unit z__SetConfig(const_sail_string, sail_int);
unit z__ListConfig(const unit u);

#ifdef __cplusplus
}
#endif

#endif
