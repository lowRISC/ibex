/*=======================================================================================*/
/*  CHERI RISCV Sail Model                                                               */
/*                                                                                       */
/*  This CHERI Sail RISC-V architecture model here, comprising all files and             */
/*  directories except for the snapshots of the Lem and Sail libraries in the            */
/*  prover_snapshots directory (which include copies of their licenses), is subject      */
/*  to the BSD two-clause licence below.                                                 */
/*                                                                                       */
/*  Copyright (c) 2017-2021                                                              */
/*    Alasdair Armstrong                                                                 */
/*    Thomas Bauereiss                                                                   */
/*    Brian Campbell                                                                     */
/*    Jessica Clarke                                                                     */
/*    Nathaniel Wesley Filardo (contributions prior to July 2020, thereafter Microsoft)  */
/*    Alexandre Joannou                                                                  */
/*    Microsoft                                                                          */
/*    Prashanth Mundkur                                                                  */
/*    Robert Norton-Wright (contributions prior to March 2020, thereafter Microsoft)     */
/*    Alexander Richardson                                                               */
/*    Peter Rugg                                                                         */
/*    Peter Sewell                                                                       */
/*                                                                                       */
/*  All rights reserved.                                                                 */
/*                                                                                       */
/*  This software was developed by SRI International and the University of               */
/*  Cambridge Computer Laboratory (Department of Computer Science and                    */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 */
/*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 */
/*  SSITH research programme.                                                            */
/*                                                                                       */
/*  This software was developed within the Rigorous Engineering of                       */
/*  Mainstream Systems (REMS) project, partly funded by EPSRC grant                      */
/*  EP/K008528/1, at the Universities of Cambridge and Edinburgh.                        */
/*                                                                                       */
/*  This project has received funding from the European Research Council                 */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation                */
/*  programme (grant agreement 789108, ELVER).                                           */
/*                                                                                       */
/*  Redistribution and use in source and binary forms, with or without                   */
/*  modification, are permitted provided that the following conditions                   */
/*  are met:                                                                             */
/*  1. Redistributions of source code must retain the above copyright                    */
/*     notice, this list of conditions and the following disclaimer.                     */
/*  2. Redistributions in binary form must reproduce the above copyright                 */
/*     notice, this list of conditions and the following disclaimer in                   */
/*     the documentation and/or other materials provided with the                        */
/*     distribution.                                                                     */
/*                                                                                       */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   */
/*  SUCH DAMAGE.                                                                         */
/*=======================================================================================*/

/* CHERI uses a boolean tag as metadata in memory. */

type mem_meta = bool

let default_meta : mem_meta = false

/* address LSB truncation/extension */
type tagaddrbits = bits(xlen - log2_cap_size)
function addr_to_tag_addr(addr : xlenbits) -> tagaddrbits = truncateLSB(addr, sizeof(xlen) - log2_cap_size)
function tag_addr_to_addr(tag_addr : tagaddrbits) -> xlenbits = tag_addr @ zeros(log2_cap_size)

/* FIXME: we should have a maximum cap_size constraint for 'n.
 * This would check that the assumption below of a max span of two regions is valid.
 */
val __WriteRAM_Meta : forall 'n. (xlenbits, atom('n), mem_meta) -> unit
function __WriteRAM_Meta(addr, width, tag) = {
  let tag_addr = addr_to_tag_addr(addr);
  if get_config_print_mem() then
    print_mem("tag[" ^ BitStr(tag_addr_to_addr(tag_addr)) ^ "] <- " ^ (if tag then "1" else "0"));
  MEMw_tag(zero_extend(tag_addr), tag);
  /* If the write crosses a cap_size alignment boundary then we need
   * to write the tag for the subsequent region.  Writes greater than
   * cap_size that might span more than two regions are not supported.
   */
  let tag_addr2 = addr_to_tag_addr(addr + width - 1);
  if tag_addr != tag_addr2 then {
    if get_config_print_mem() then
      print_mem("tag[" ^ BitStr(tag_addr_to_addr(tag_addr2)) ^ "] <- " ^ (if tag then "1" else "0"));
    MEMw_tag(zero_extend(tag_addr2), tag);
  }
}

/* FIXME: we should have a maximum cap_size constraint for 'n. */
val __ReadRAM_Meta  : forall 'n. (xlenbits, atom('n)) -> mem_meta
function __ReadRAM_Meta(addr, width) = {
  let tag_addr = addr_to_tag_addr(addr);
  let tag = MEMr_tag(zero_extend(tag_addr));
  if get_config_print_mem() then
    print_mem("tag[R," ^ BitStr(tag_addr_to_addr(tag_addr)) ^ "] -> " ^ (if tag then "1" else "0"));
  tag
}
