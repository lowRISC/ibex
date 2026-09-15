/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

function fetch() -> FetchResult = {
  rvfi_inst_data[rvfi_order] = minstret;
  rvfi_pc_data[rvfi_pc_rdata] = zero_extend(get_arch_pc());
  rvfi_inst_data[rvfi_mode] = zero_extend(privLevel_to_bits(cur_privilege));
  rvfi_inst_data[rvfi_ixl] = zero_extend(misa[MXL]);

  /* First allow extensions to check pc */
  match ext_fetch_check_pc(PC, PC) {
    Ext_FetchAddr_Error(e)   => F_Ext_Error(e),
    Ext_FetchAddr_OK(use_pc) => {
      /* then check PC alignment */
      if   (use_pc[0] != bitzero | (use_pc[1] != bitzero & not(haveRVC())))
      then F_Error(E_Fetch_Addr_Align(), PC)
      else match translateAddr(use_pc, Execute()) {
        TR_Failure(e, _) => F_Error(e, PC),
        TR_Address(_, _) => {
          let i = rvfi_instruction[rvfi_insn];
          rvfi_inst_data->rvfi_insn()   = zero_extend(i);
          if   (i[1 .. 0] != 0b11)
          then F_RVC(i[15 .. 0])
          else {
            /* fetch PC check for the next instruction granule */
            PC_hi : xlenbits = PC + 2;
            match ext_fetch_check_pc(PC, PC_hi) {
              Ext_FetchAddr_Error(e)      => F_Ext_Error(e),
              Ext_FetchAddr_OK(use_pc_hi) =>
                match translateAddr(use_pc_hi, Execute()) {
                  TR_Failure(e, _) => F_Error(e, PC),
                  TR_Address(_, _) => F_Base(i)
              }
            }
          }
        }
      }
    }
  }
}
