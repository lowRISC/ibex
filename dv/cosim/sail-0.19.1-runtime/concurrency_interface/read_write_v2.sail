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

$ifndef _CONCURRENCY_INTERFACE_READ_WRITE_V2
$define _CONCURRENCY_INTERFACE_READ_WRITE_V2

$include <concurrency_interface/common.sail>

/* This file present the Sail interface for reading and writing memory. This
   interface can instanciated either at the user-mode level when Sail is used to
   reason about user-mode program, in which case the addresses used are the
   program addresses: virtual addresses.

   It can also be instanciated at the system level if address translation is
   implemented in Sail, in which case the addresses will be physical addresses.

   This interface depends on a few parameters:
   - addr_size : Int, The size of addresses to be used, in bits.
   - addr_space : Type, An extra tag on the address to identify it's address
     space. For Arm this is Secure/Non-Secure, for all other architecture this
     should probably be unit.
   - mem_acc : Type, An architecture specific description of the access kind.
     This may also contain arbitrary architecture specific metadata about the
     access.
   - abort : Type, The type of memory aborts/access failure: To be
     returned when the access has failed. In system-level instantiations, this is
     expected to be for physcial memory abort (e.g. SError in Arm)
   - CHERI : Bool, Whether CHERI is active on this architecture, which means the
     memory has capability tags
   - cap_size_log : Int, If CHERI is on, the log2 of the size of capabilities in
     bytes. For example for 16 bytes capabilities, this should be 4.

   Arm-MTE-like tags are not supported by this API, but can be added separately
   as an extension
*/


/* This type represent a Request to read a section of memory. It requests
   reading 'n bytes of data and 'nt capabilities tags (if CHERI is off, 'nt must
   be 0) The actual footprint read is max('n, 'cap_size * 'nt). If 'n is smaller
   than this value, the extra bytes are discarded. */
$option -lem_extern_type Mem_read_request
$option -coq_extern_type Mem_read_request
$option -lean_extern_type Mem_read_request
struct Mem_read_request('n : Int, 'nt : Int, 'addr_size : Int, 'addr_space : Type,
    'mem_acc : Type), 'n >= 0 & 'nt >= 0 & 'addr_size > 0 = {
  access_kind : 'mem_acc,
  address : bits('addr_size),
  address_space : 'addr_space,
  size : int('n),
  num_tag : int('nt), // This is CHERI tags, MTE-like tags are not supported
}

$ifdef SYMBOLIC

register __monomorphize_reads: bool = false
register __monomorphize_writes: bool = false

$else

let __monomorphize_reads: bool = false
let __monomorphize_writes: bool = false

$endif

/* Requests a memory read. Return 'n bytes and 'nt tags */
outcome sail_mem_read : forall 'n 'nt, 'n >= 0 & (if 'CHERI then 'nt >= 0 else 'nt == 0).
  Mem_read_request('n, 'nt, 'addr_size, 'addr_space, 'mem_acc)
      -> result((vector('n, bits(8)), vector('nt, bool)), 'abort)
with
  'addr_size : Int,
  'addr_space : Type,
  'mem_acc : Type,
  'abort : Type,
  'CHERI : Bool,
  'cap_size_log : Int
constraint 'addr_size > 0 & 'cap_size_log >= 0
= {
    // Generic classifiers for mem_acc to enable some level of architechture generic programming

    // Is the access an explicit data access. That means it must respect basic
    // coherency rule and in particular behave sequentially if used by a single
    // thread without need for cache invalidation (if the backend memory is regular RAM)
    val mem_acc_is_explicit : 'mem_acc -> bool

    // Is the access an instruction fetch access
    val mem_acc_is_ifetch : 'mem_acc -> bool

    // Is the access a page-table walk access (from the MMU)
    val mem_acc_is_ttw : 'mem_acc -> bool

    // The remaining classifiers are only for explicit accesses,
    // They should all imply mem_acc_is_explicit.

    // Those 3 function classify the release/acquire strength
    val mem_acc_is_relaxed : 'mem_acc -> bool
    val mem_acc_is_rel_acq_rcpc : 'mem_acc -> bool
    val mem_acc_is_rel_acq_rcsc : 'mem_acc -> bool

    // Those 3 function classify whether a call is part of atomic/exclusive
    // sequence or not
    val mem_acc_is_standalone : 'mem_acc -> bool
    val mem_acc_is_exclusive : 'mem_acc -> bool
    val mem_acc_is_atomic_rmw : 'mem_acc -> bool

    impl emulator_or_isla(request) = {
        let address : {'as, 'as in {32, 64}. bits('as)} =
            if length(request.address) <= 32
            then sail_zero_extend(request.address, 32)
            else if length(request.address) <= 64
            then sail_zero_extend(request.address, 64)
            // TODO maybe support addresses bigger than 64 bits
            else {assert(false);sail_zeros(64)};
        // In Isla, the address of an instruction fetch must be concrete
        let address =
            if mem_acc_is_ifetch(request.access_kind) | __monomorphize_reads
            then __monomorphize(address)
            else address;
        let tags : vector('nt, bool) = if constraint('CHERI) then {
            var tags : vector('nt, bool) = vector_init(request.num_tag, false);
            let cap_size = 2 ^ 'cap_size_log;
            let tag_address = address & sail_shiftleft(sail_ones(length(address)), 'cap_size_log);
            foreach(i from 0 to (request.num_tag - 1)) {
                if length(address) == 32 then {
                    tags[i] = read_tag#(32, tag_address + i * cap_size)
                } else {
                    tags[i] = read_tag#(64, tag_address + i * cap_size)
                }
            };
            tags
        } else [];
        let value = if request.size > 0 then {
            let valuebv = if mem_acc_is_exclusive(request.access_kind) then {
                if length(address) == 32 then {
                    read_mem_exclusive#(request, 32, address, request.size)
                } else {
                    read_mem_exclusive#(request, 64, address, request.size)
                }
            } else if mem_acc_is_ifetch(request.access_kind) then {
                if length(address) == 32 then {
                    read_mem_ifetch#(request, 32, address, request.size)
                } else {
                    read_mem_ifetch#(request, 64, address, request.size)
                }
            } else {
                if length(address) == 32 then {
                    read_mem#(request, 32, address, request.size)
                } else {
                    read_mem#(request, 64, address, request.size)
                }
            };
            to_bytes_le(request.size, valuebv)
        } else {
            vector_init(0, sail_zeros(8))
        };
        Ok(value, tags)
    }
}

/* This type represent a request to write a range of memory. It requests
   writing 'n bytes of data and 'nt capabilities tags (if CHERI is off, 'nt must
   be 0). 'n can be 0 to write only CHERI tags */
$option -lem_extern_type Mem_write_request
$option -coq_extern_type Mem_write_request
$option -lean_extern_type Mem_write_request
struct Mem_write_request('n : Int, 'nt : Int, 'addr_size : Int, 'addr_space : Type,
    'mem_acc : Type), 'n >= 0 & 'nt >= 0 & 'addr_size > 0 = {
  access_kind : 'mem_acc,
  address : bits('addr_size),
  address_space : 'addr_space,
  size : int('n),
  num_tag : int('nt),
  value : vector('n, bits(8)),
  tags : vector('nt, bool),
}

/* Requests a memory write. If the write cannot happen due to
   atomicity/exclusive constraints, then the execution path is discarded as
   impossible (size-0 non deterministic choice). Is the responsability of the
   Sail model to do the proper non-determinitic choices beforehand */
outcome sail_mem_write : forall 'n 'nt, 'n >= 0 & (if 'CHERI then 'nt >= 0 else 'nt == 0).
  Mem_write_request('n, 'nt, 'addr_size, 'addr_space, 'mem_acc)
      -> result(unit, 'abort)
with
  'addr_size : Int,
  'addr_space : Type,
  'mem_acc : Type,
  'abort : Type,
  'CHERI : Bool,
  'cap_size_log : Int
constraint 'addr_size > 0 & 'cap_size_log >= 0
= {
    // See sail_mem_read for documentation
    val mem_acc_is_explicit : 'mem_acc -> bool
    val mem_acc_is_ifetch : 'mem_acc -> bool
    val mem_acc_is_ttw : 'mem_acc -> bool
    val mem_acc_is_relaxed : 'mem_acc -> bool
    val mem_acc_is_rel_acq_rcpc : 'mem_acc -> bool
    val mem_acc_is_rel_acq_rcsc : 'mem_acc -> bool
    val mem_acc_is_standalone : 'mem_acc -> bool
    val mem_acc_is_exclusive : 'mem_acc -> bool
    val mem_acc_is_atomic_rmw : 'mem_acc -> bool

    impl emulator_or_isla(request) = {
        let address : {'as, 'as in {32, 64}. bits('as)} =
            if length(request.address) <= 32
            then sail_zero_extend(request.address, 32)
            else if length(request.address) <= 64
            then sail_zero_extend(request.address, 64)
            else {assert(false); sail_zeros(64)};

        let address = if __monomorphize_writes then __monomorphize(address) else address;
        if constraint('CHERI) then {
            let cap_size = 2 ^ 'cap_size_log;
            let tag_address = address & sail_shiftleft(sail_ones(length(address)), 'cap_size_log);
            let tag_footprint = max_int(tdiv_int(request.size + cap_size - 1, cap_size), request.num_tag);
            foreach(i from 0 to (tag_footprint - 1)) {
                let tag_val = if (i >= request.num_tag) then false else request.tags[i];
                if length(address) == 32 then {
                    write_tag#(32, tag_address + i * cap_size, tag_val)
                } else {
                    write_tag#(64, tag_address + i * cap_size, tag_val)
                }
            };
        };
        if request.size > 0 then {
            let value = from_bytes_le(request.size, request.value);
            if mem_acc_is_exclusive(request.access_kind) then {
                if length(address) == 32 then {
                    let _ = write_mem_exclusive#(request, 32, address, request.size, value)
                } else {
                    let _ = write_mem_exclusive#(request, 64, address, request.size, value)
                }
            } else {
                if length(address) == 32 then {
                    let _ = write_mem#(request, 32, address, request.size, value)
                } else {
                    let _ = write_mem#(request, 64, address, request.size, value);
                }
            }
        };
        Ok(())
    }
}

// Used when we want a non memory read/write to appear in Isla's addr relation
$iftarget isla
val sail_address_announce = impure "address_announce" : forall 'addrsize, 'addrsize in {32, 64}. (int('addrsize), bits('addrsize)) -> unit
$else
val sail_address_announce : forall 'addrsize, 'addrsize in {32, 64}. (int('addrsize), bits('addrsize)) -> unit

function sail_address_announce(_, _) = ()
$endif

$endif
