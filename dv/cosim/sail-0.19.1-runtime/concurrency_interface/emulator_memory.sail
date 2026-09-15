/*==========================================================================*/
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
/*==========================================================================*/

$sail_internal

$ifndef _EMULATOR_MEMORY

$ifdef _DEFAULT_DEC
$include <vector_dec.sail>
$else
$include <vector_inc.sail>
$endif

$iftarget c
$define _EMULATOR_MEMORY_PRIMOPS
$endif

$iftarget ocaml
$define _EMULATOR_MEMORY_PRIMOPS
$endif

$iftarget systemverilog
$define _EMULATOR_MEMORY_PRIMOPS
$endif

$ifdef INTERACTIVE
$define _EMULATOR_MEMORY_PRIMOPS
$endif

//! Read memory
$iftarget isla
val read_mem# = impure "read_mem" : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)
$else
val read_mem# : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

$ifdef _EMULATOR_MEMORY_PRIMOPS
$[sv_function]
val __read_mem# = impure "emulator_read_mem" : forall 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

function read_mem#(_, addrsize, addr, n) = __read_mem#(addrsize, addr, n)
$endif
$endif

//! Read memory, but signal to the emulator that this is an ifetch read
$iftarget isla
val read_mem_ifetch# = impure "read_mem_ifetch" : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)
$else
val read_mem_ifetch# : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

$ifdef _EMULATOR_MEMORY_PRIMOPS
$[sv_function]
val __read_mem_ifetch# = impure "emulator_read_mem_ifetch" : forall 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

function read_mem_ifetch#(_, addrsize, addr, n) = __read_mem_ifetch#(addrsize, addr, n)
$endif
$endif

//! Read memory, and signal to the emulator that this read should be treated as an exclusive access
$iftarget isla
val read_mem_exclusive# = impure "read_mem_exclusive" : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)
$else
val read_mem_exclusive# : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

$ifdef _EMULATOR_MEMORY_PRIMOPS
$[sv_function]
val __read_mem_exclusive# = impure "emulator_read_mem_exclusive" : forall 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

function read_mem_exclusive#(_, addrsize, addr, n) = __read_mem_exclusive#(addrsize, addr, n)
$endif
$endif

//! Write memory
$iftarget isla
val write_mem# = impure "write_mem" : forall ('a: Type) 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool
$else
val write_mem# : forall ('a: Type) 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

$ifdef _EMULATOR_MEMORY_PRIMOPS
$[sv_module { writes_memory = true }]
val __write_mem# = impure "emulator_write_mem" : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

function write_mem#(_, addrsize, addr, n, value) = __write_mem#(addrsize, addr, n, value)
$endif
$endif

//! Write memory, and signal to the emulator that this read should be treated as an exclusive access
$iftarget isla
val write_mem_exclusive# = impure "write_mem_exclusive" : forall ('a: Type) 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool
$else
val write_mem_exclusive# : forall ('a: Type) 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

$ifdef _EMULATOR_MEMORY_PRIMOPS
$[sv_module { writes_memory = true }]
val __write_mem_exclusive# = impure "emulator_write_mem_exclusive" : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

function write_mem_exclusive#(_, addrsize, addr, n, value) = __write_mem_exclusive#(addrsize, addr, n, value)
$endif
$endif

$[sv_function]
val read_tag# = impure "emulator_read_tag"  : forall 'addrsize, 'addrsize in {32, 64}. (int('addrsize), bits('addrsize)) -> bool

$[sv_module { writes_memory = true }]
val write_tag# = impure "emulator_write_tag" : forall 'addrsize, 'addrsize in {32, 64}. (int('addrsize), bits('addrsize), bool) -> unit

$endif
