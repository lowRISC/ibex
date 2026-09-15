/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Definitions for floating point registers (F and D extensions) */

/* default register type */
type fregtype = flenbits

/* default zero register */
let zero_freg : fregtype = zero_extend(0x0)

/* default register printer */
val FRegStr : fregtype -> string
function FRegStr(r) = BitStr(r)

/* conversions */

val fregval_from_freg : fregtype -> flenbits
function fregval_from_freg(r) = r

val fregval_into_freg : flenbits -> fregtype
function fregval_into_freg(v) = v


/* Rounding Mode
    Rounding modes occur as a 3-bit field in F,D instructions,
    and also as a 3-bit 'frm' field in the 'fcsr' CSR.
    RISC-V uses the following IEEE-defined rounding modes.
*/

enum f_madd_op_H = {FMADD_H, FMSUB_H, FNMSUB_H, FNMADD_H}

enum f_bin_rm_op_H = {FADD_H, FSUB_H, FMUL_H, FDIV_H}

enum f_un_rm_op_H = {FSQRT_H, FCVT_W_H, FCVT_WU_H, FCVT_H_W, FCVT_H_WU,    // RV32 and RV64
                     FCVT_H_S, FCVT_H_D, FCVT_S_H, FCVT_D_H,
                     FCVT_L_H, FCVT_LU_H, FCVT_H_L, FCVT_H_LU}             // RV64 only

enum f_un_op_H = {FCLASS_H, FMV_X_H, FMV_H_X}    /* RV32 and RV64 */

enum f_bin_op_H = {FSGNJ_H, FSGNJN_H, FSGNJX_H, FMIN_H, FMAX_H, FEQ_H, FLT_H, FLE_H}

enum rounding_mode = {RM_RNE, RM_RTZ, RM_RDN, RM_RUP, RM_RMM, RM_DYN}

enum f_madd_op_S = {FMADD_S, FMSUB_S, FNMSUB_S, FNMADD_S}

enum f_bin_rm_op_S = {FADD_S, FSUB_S, FMUL_S, FDIV_S}

enum f_un_rm_op_S = {FSQRT_S, FCVT_W_S, FCVT_WU_S, FCVT_S_W, FCVT_S_WU,    // RV32 and RV64
                     FCVT_L_S, FCVT_LU_S, FCVT_S_L, FCVT_S_LU}             // RV64 only

enum f_un_op_S = {FCLASS_S, FMV_X_W, FMV_W_X}    /* RV32 and RV64 */

enum f_bin_op_S = {FSGNJ_S, FSGNJN_S, FSGNJX_S, FMIN_S, FMAX_S, FEQ_S, FLT_S, FLE_S}

enum f_madd_op_D = {FMADD_D, FMSUB_D, FNMSUB_D, FNMADD_D}

enum f_bin_rm_op_D = {FADD_D, FSUB_D, FMUL_D, FDIV_D}

enum f_un_rm_op_D = {FSQRT_D, FCVT_W_D, FCVT_WU_D, FCVT_D_W, FCVT_D_WU,    // RV32 and RV64
                     FCVT_S_D, FCVT_D_S,
                     FCVT_L_D, FCVT_LU_D, FCVT_D_L, FCVT_D_LU}             // RV64 only

enum f_bin_op_D = {FSGNJ_D, FSGNJN_D, FSGNJX_D, FMIN_D, FMAX_D, FEQ_D, FLT_D, FLE_D}

enum f_un_op_D = {FCLASS_D,            /* RV32 and RV64 */
                  FMV_X_D, FMV_D_X}    /* RV64 only */
