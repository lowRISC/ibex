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

$ifndef _REGFP
$define _REGFP

/* iR : input registers,
 * oR : output registers,
 * aR : registers feeding into the memory address */

/* branch instructions currently are not writing to NIA */

union regfp = {
   RFull : string,
   RSlice : (string,nat,nat),
   RSliceBit : (string,nat),
   RField : (string,string)
}

type regfps = list(regfp)

union niafp = {
  NIAFP_successor : unit,
  NIAFP_concrete_address : bits(64),
  NIAFP_indirect_address : unit
}

type niafps = list(niafp)

/* only for MIPS */
$option --coq-extern-type diafp
union diafp = {
  DIAFP_none : unit,
  DIAFP_concrete : bits(64),
  DIAFP_reg : regfp
}

$option --coq-extern-type read_kind
$option --lem-extern-type read_kind
enum read_kind = {
  Read_plain,
  Read_reserve,
  Read_acquire,
  Read_exclusive,
  Read_exclusive_acquire,
  Read_stream,
  Read_ifetch,
  Read_RISCV_acquire,
  Read_RISCV_strong_acquire,
  Read_RISCV_reserved,
  Read_RISCV_reserved_acquire,
  Read_RISCV_reserved_strong_acquire,
  Read_X86_locked
}

$option --coq-extern-type write_kind
$option --lem-extern-type write_kind
enum write_kind = {
  Write_plain,
  Write_conditional,
  Write_release,
  Write_exclusive,
  Write_exclusive_release,
  Write_RISCV_release,
  Write_RISCV_strong_release,
  Write_RISCV_conditional,
  Write_RISCV_conditional_release,
  Write_RISCV_conditional_strong_release,
  Write_X86_locked
}

$option --coq-extern-type barrier_kind
$option --lem-extern-type barrier_kind
$ifdef ARM_SPEC
enum barrier_kind = {
  Barrier_DMB_SY,
  Barrier_DMB_ST,
  Barrier_DMB_LD,
  Barrier_DMB_ISH,
  Barrier_DMB_ISHST,
  Barrier_DMB_ISHLD,
  Barrier_DMB_NSH,
  Barrier_DMB_NSHST,
  Barrier_DMB_NSHLD,
  Barrier_DMB_OSH,
  Barrier_DMB_OSHST,
  Barrier_DMB_OSHLD,
  Barrier_DSB_SY,
  Barrier_DSB_ST,
  Barrier_DSB_LD,
  Barrier_DSB_ISH,
  Barrier_DSB_ISHST,
  Barrier_DSB_ISHLD,
  Barrier_DSB_NSH,
  Barrier_DSB_NSHST,
  Barrier_DSB_NSHLD,
  Barrier_DSB_OSH,
  Barrier_DSB_OSHST,
  Barrier_DSB_OSHLD,
  Barrier_ISB
}
$else
$option --coq-extern-type a64_barrier_domain
$option --lem-extern-type a64_barrier_domain
enum a64_barrier_domain = {
  A64_FullShare,
  A64_InnerShare,
  A64_OuterShare,
  A64_NonShare
}

$option --coq-extern-type a64_barrier_type
$option --lem-extern-type a64_barrier_type
enum a64_barrier_type = {
  A64_barrier_all,
  A64_barrier_LD,
  A64_barrier_ST
}

union barrier_kind = {
  Barrier_Sync : unit,
  Barrier_LwSync : unit,
  Barrier_Eieio : unit,
  Barrier_Isync : unit,
  Barrier_DMB : (a64_barrier_domain, a64_barrier_type),
  Barrier_DSB : (a64_barrier_domain, a64_barrier_type),
  Barrier_ISB : unit,
  Barrier_MIPS_SYNC : unit,
  Barrier_RISCV_rw_rw : unit,
  Barrier_RISCV_r_rw : unit,
  Barrier_RISCV_r_r : unit,
  Barrier_RISCV_rw_w : unit,
  Barrier_RISCV_w_w : unit,
  Barrier_RISCV_w_rw : unit,
  Barrier_RISCV_rw_r : unit,
  Barrier_RISCV_r_w : unit,
  Barrier_RISCV_w_r : unit,
  Barrier_RISCV_tso : unit,
  Barrier_RISCV_i : unit,
  Barrier_x86_MFENCE : unit
}
$endif

$option --coq-extern-type trans_kind
$option --lem-extern-type trans_kind
enum trans_kind = {
  Transaction_start,
  Transaction_commit,
  Transaction_abort
}

/* cache maintenance instructions */
$option --coq-extern-type cache_op_kind
$option --lem-extern-type cache_op_kind
enum cache_op_kind = {
  /* AArch64 DC */
  Cache_op_D_IVAC, Cache_op_D_ISW,  Cache_op_D_CSW,  Cache_op_D_CISW,
  Cache_op_D_ZVA,  Cache_op_D_CVAC, Cache_op_D_CVAU, Cache_op_D_CIVAC,
  /* AArch64 IC */
  Cache_op_I_IALLUIS, Cache_op_I_IALLU, Cache_op_I_IVAU
}


$option --coq-extern-type instruction_kind
$option --lem-extern-type instruction_kind
union instruction_kind = {
  IK_barrier : barrier_kind,
  IK_mem_read : read_kind,
  IK_mem_write : write_kind,
  IK_mem_rmw : (read_kind, write_kind),
  IK_branch : unit,
  IK_trans : trans_kind,
  IK_simple : unit,
  IK_cache_op : cache_op_kind
}

val __read_mem
  = impure { ocaml: "Platform.read_mem", c: "platform_read_mem", _: "read_mem" }
  : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
  (read_kind, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

val __read_memt
  = impure { ocaml: "Platform.read_memt", c: "platform_read_memt", _: "read_memt" }
  : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
  (read_kind, bits('addrsize), int('n)) -> (bits(8 * 'n), bit)

val __write_mem_ea
  = impure { ocaml: "Platform.write_mem_ea", c: "platform_write_mem_ea", _: "write_mem_ea" }
  : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, int('addrsize), bits('addrsize), int('n)) -> unit

val __write_mem
  = impure { ocaml: "Platform.write_mem", c: "platform_write_mem", _: "write_mem" }
  : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

val __write_memt
  = impure { ocaml: "Platform.write_memt", c: "platform_write_memt", _: "write_memt" }
  : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
  (write_kind, bits('addrsize), int('n), bits(8 * 'n), bit) -> bool

val __write_tag
  = impure { ocaml: "Platform.write_tag", c: "platform_write_tag", _: "write_tag" }
  : forall 'addrsize, 'addrsize in {32, 64}.
  (write_kind, bits('addrsize), bit) -> bool

val __excl_res
  = impure { ocaml: "Platform.excl_res", c: "platform_excl_res", _: "excl_result" }
  : unit -> bool

val __barrier
  = impure { ocaml: "Platform.barrier", c: "platform_barrier", _: "barrier" }
  : barrier_kind -> unit

val __branch_announce
  = impure { ocaml: "Platform.branch_announce", c: "platform_branch_announce", _ : "branch_announce" }
  : forall 'addrsize, 'addrsize in {32, 64}.
  (int('addrsize), bits('addrsize)) -> unit

val __cache_maintenance
  = impure { ocaml: "Platform.cache_maintenance", c: "platform_cache_maintenance", _ : "cache_maintenance" }
  : forall 'addrsize, 'addrsize in {32, 64}.
  (cache_op_kind, int('addrsize), bits('addrsize)) -> unit

val __instr_announce
  = impure { ocaml: "Platform.instr_announce", c: "platform_instr_announce", _: "instr_announce" }
  : forall 'n, 'n > 0.
  bits('n) -> unit

$endif
