/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Architectural state for the 'N' user-level interrupts standard extension. */

/* ustatus reveals a subset of mstatus */
bitfield Ustatus : xlenbits = {
  UPIE : 4,
  UIE  : 0
}

/* This is a view, so there is no register defined. */
function lower_sstatus(s : Sstatus) -> Ustatus = {
  let u = Mk_Ustatus(zero_extend(0b0));
  let u = [u with UPIE = s[UPIE]];
  let u = [u with UIE = s[UIE]];
  u
}

function lift_ustatus(s : Sstatus, u : Ustatus) -> Sstatus = {
  let s = [s with UPIE = u[UPIE]];
  let s = [s with UIE = u[UIE]];
  s
}

function legalize_ustatus(m : Mstatus, v : xlenbits) -> Mstatus = {
  let u = Mk_Ustatus(v);
  let s = lower_mstatus(m);     // lower current mstatus to sstatus
  let s = lift_ustatus(s, u);   // get updated sstatus
  let m = lift_sstatus(m, s);   // lift it to an updated mstatus
  m
}

bitfield Uinterrupts : xlenbits = {
  UEI : 8,  /* external interrupt */
  UTI : 4,  /* timer interrupt    */
  USI : 0   /* software interrupt */
}

/* Provides the uip read view of sip (s) as delegated by sideleg (d). */
function lower_sip(s : Sinterrupts, d : Sinterrupts) -> Uinterrupts = {
  let u : Uinterrupts = Mk_Uinterrupts(zero_extend(0b0));
  let u = [u with UEI = s[UEI] & d[UEI]];
  let u = [u with UTI = s[UTI] & d[UTI]];
  let u = [u with USI = s[USI] & d[USI]];
  u
}

/* Provides the uie read view of sie as delegated by sideleg. */
function lower_sie(s : Sinterrupts, d : Sinterrupts) -> Uinterrupts = {
  let u : Uinterrupts = Mk_Uinterrupts(zero_extend(0b0));
  let u = [u with UEI = s[UEI] & d[UEI]];
  let u = [u with UTI = s[UTI] & d[UTI]];
  let u = [u with USI = s[USI] & d[USI]];
  u
}

/* Returns the new value of sip from the previous sip (o) and the written uip (u) as delegated by sideleg (d). */
function lift_uip(o : Sinterrupts, d : Sinterrupts, u : Uinterrupts) -> Sinterrupts = {
  let s : Sinterrupts = o;
  let s = if d[USI] == 0b1 then [s with USI = u[USI]] else s;
  s
}

function legalize_uip(s : Sinterrupts, d : Sinterrupts, v : xlenbits) -> Sinterrupts = {
  lift_uip(s, d, Mk_Uinterrupts(v))
}

/* Returns the new value of sie from the previous sie (o) and the written uie (u) as delegated by sideleg (d). */
function lift_uie(o : Sinterrupts, d : Sinterrupts, u : Uinterrupts) -> Sinterrupts = {
  let s : Sinterrupts = o;
  let s = if d[UEI] == 0b1 then [s with UEI = u[UEI]] else s;
  let s = if d[UTI] == 0b1 then [s with UTI = u[UTI]] else s;
  let s = if d[USI] == 0b1 then [s with USI = u[USI]] else s;
  s
}

function legalize_uie(s : Sinterrupts, d : Sinterrupts, v : xlenbits) -> Sinterrupts = {
  lift_uie(s, d, Mk_Uinterrupts(v))
}

register utvec    : Mtvec
register uscratch : xlenbits
register uepc     : xlenbits
register ucause   : Mcause
register utval    : xlenbits
