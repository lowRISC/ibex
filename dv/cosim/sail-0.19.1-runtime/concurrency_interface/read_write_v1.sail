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

$ifndef _CONCURRENCY_INTERFACE_READ_WRITE_V1
$define _CONCURRENCY_INTERFACE_READ_WRITE_V1

$include <concurrency_interface/common.sail>


$option -lem_extern_type Access_variety
$option -coq_extern_type Access_variety
$option -lean_extern_type Access_variety
enum Access_variety = {
  AV_plain,
  AV_exclusive,
  AV_atomic_rmw
}

$option -lem_extern_type Access_strength
$option -coq_extern_type Access_strength
$option -lean_extern_type Access_strength
enum Access_strength = {
  AS_normal,
  AS_rel_or_acq, // Release or acquire
  AS_acq_rcpc // Release-consistency with processor consistency
}

$option -lem_extern_type Explicit_access_kind
$option -coq_extern_type Explicit_access_kind
$option -lean_extern_type Explicit_access_kind
struct Explicit_access_kind = {
  variety : Access_variety,
  strength : Access_strength
}

$option -lem_extern_type Access_kind
$option -coq_extern_type Access_kind
$option -lean_extern_type Access_kind
union Access_kind('arch_ak : Type) = {
  AK_explicit: Explicit_access_kind,
  AK_ifetch : unit, // Instruction fetch
  AK_ttw : unit, // Translation table walk
  AK_arch : 'arch_ak // Architecture specific type of access
}

$option -lem_extern_type Mem_read_request
$option -coq_extern_type Mem_read_request
$option -lean_extern_type Mem_read_request
struct Mem_read_request('n : Int, 'vasize : Int, 'pa : Type, 'ts : Type,
                        'arch_ak : Type), 'n > 0 & 'vasize >= 0 = {
  access_kind : Access_kind('arch_ak),
  // There may not always be a virtual address, e.g. when translation is off.
  // Additionally, translate reads don't have a (VA, PA) pair in the
  // translation relation anyway.
  va : option(bits('vasize)),
  pa : 'pa,
  translation : 'ts,
  size : int('n),
  tag : bool
}

val mem_read_request_is_exclusive : forall 'n 'vasize ('pa 'translation_summary 'arch_ak : Type), 'n > 0 & 'vasize > 0.
  Mem_read_request('n, 'vasize, 'pa, 'translation_summary, 'arch_ak) -> bool

function mem_read_request_is_exclusive(request) = {
    match request.access_kind {
        AK_explicit(eak) => match eak.variety {
            AV_exclusive => true,
            _ => false,
        },
        _ => false,
    }
}

val mem_read_request_is_ifetch : forall 'n 'vasize ('pa 'translation_summary 'arch_ak : Type), 'n > 0 & 'vasize > 0.
  Mem_read_request('n, 'vasize, 'pa, 'translation_summary, 'arch_ak) -> bool

function mem_read_request_is_ifetch(request) = {
    match request.access_kind {
        AK_ifetch() => true,
        _ => false,
    }
}

$ifdef SYMBOLIC

register __monomorphize_reads: bool = false
register __monomorphize_writes: bool = false

$else

let __monomorphize_reads: bool = false
let __monomorphize_writes: bool = false

$endif

outcome sail_mem_read : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
  Mem_read_request('n, 'vasize, 'pa, 'translation_summary, 'arch_ak)
      -> result((bits(8 * 'n), option(bool)), 'abort)
with
  'pa : Type,
  'translation_summary : Type,
  'arch_ak : Type,
  'abort : Type
= {
    val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

    impl emulator_or_isla(request) = {
        let pa = pa_bits(request.pa);
        // In Isla, the address of an instruction fetch must be concrete
        let pa = if mem_read_request_is_ifetch(request) | __monomorphize_reads then __monomorphize(pa) else pa;
        let tag: option(bool) = if request.tag then {
            if length(pa) == 32 then {
                Some(read_tag#(32, pa))
            } else {
                Some(read_tag#(64, pa))
            }
        } else {
            None()
        };
        if mem_read_request_is_exclusive(request) then {
            if length(pa) == 32 then {
                Ok((read_mem_exclusive#(request, 32, pa, request.size), tag))
            } else {
                Ok((read_mem_exclusive#(request, 64, pa, request.size), tag))
            }
        } else if mem_read_request_is_ifetch(request) then {
            if length(pa) == 32 then {
                Ok((read_mem_ifetch#(request, 32, pa, request.size), tag))
            } else {
                Ok((read_mem_ifetch#(request, 64, pa, request.size), tag))
            }
        } else {
            if length(pa) == 32 then {
                Ok((read_mem#(request, 32, pa, request.size), tag))
            } else {
                Ok((read_mem#(request, 64, pa, request.size), tag))
            }
        }
    }
}

$option -lem_extern_type Mem_write_request
$option -coq_extern_type Mem_write_request
$option -lean_extern_type Mem_write_request
struct Mem_write_request('n : Int, 'vasize : Int, 'pa : Type, 'ts : Type,
                         'arch_ak : Type), 'n > 0 & 'vasize >= 0 = {
  access_kind : Access_kind('arch_ak),
  va : option(bits('vasize)),
  pa : 'pa,
  translation : 'ts,
  size : int('n),
  value : option(bits(8 * 'n)),
  tag : option(bool),
}

val mem_write_request_is_exclusive : forall 'n 'vasize ('pa 'translation_summary 'arch_ak : Type), 'n > 0 & 'vasize > 0.
  Mem_write_request('n, 'vasize, 'pa, 'translation_summary, 'arch_ak) -> bool

function mem_write_request_is_exclusive(request) = {
    match request.access_kind {
        AK_explicit(eak) => match eak.variety {
            AV_exclusive => true,
            _ => false,
        },
        _ => false,
    }
}

// the bool in the result is for the success/failure of a write-exclusive or a CAS, i.e.
outcome sail_mem_write : forall 'n 'vasize, 'n > 0 & 'vasize > 0.
  Mem_write_request('n, 'vasize, 'pa, 'translation_summary, 'arch_ak)
      -> result(option(bool), 'abort)
with
  'pa : Type,
  'translation_summary : Type,
  'arch_ak : Type,
  'abort : Type
= {
    val pa_bits : 'pa -> {'pasize, 'pasize in {32, 64}. bits('pasize)}

    impl emulator_or_isla(request) = {
        let pa = pa_bits(request.pa);
        let pa = if __monomorphize_writes then __monomorphize(pa) else pa;
        let b: bool = match request.value {
            Some(value) => if mem_write_request_is_exclusive(request) then {
                if length(pa) == 32 then {
                    write_mem_exclusive#(request, 32, pa, request.size, value)
                } else {
                    write_mem_exclusive#(request, 64, pa, request.size, value)
                }
            } else {
                if length(pa) == 32 then {
                    write_mem#(request, 32, pa, request.size, value)
                } else {
                    write_mem#(request, 64, pa, request.size, value)
                }
            },
            None() => true
        };
        match request.tag {
            Some(tag) => if length(pa) == 32 then {
                write_tag#(32, pa, tag)
            } else {
                write_tag#(64, pa, tag)
            },
            None() => ()
        };
        Ok(Some(b))
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
