# Copyright lowRISC contributors.
# Copyright 2024 University of Oxford, see also CREDITS.md.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# The underlying commands and reports of this script are copyrighted by Cadence.
# We thank Cadence for granting permission to share our research to help
# promote and foster the next generation of innovators.
# Original author: Louis-Emile Ploix
# SPDX-License-Identifier: Apache-2.0

set_prove_cache_path jgproofs
set_prove_cache on
set_prove_cache_mode coi

set_prove_per_property_time_limit 10s

set ibex_root ../../
set sail_lib_dir $env(SAIL_DIR)/lib/sv
set prim $ibex_root/vendor/lowrisc_ip/ip/prim/rtl/
set dv $ibex_root/vendor/lowrisc_ip/dv/sv/dv_utils/

analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_pkg.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_alu.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_compressed_decoder.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_controller.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_cs_registers.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_decoder.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_ex_block.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_id_stage.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_if_stage.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_wb_stage.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_load_store_unit.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_multdiv_slow.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_counter.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_multdiv_fast.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_prefetch_buffer.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_fetch_fifo.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_pmp.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_core.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_csr.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_register_file_ff.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/vendor/lowrisc_ip/ip/prim/rtl/prim_secded_pkg.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/vendor/lowrisc_ip/ip/prim/rtl/prim_assert.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/vendor/lowrisc_ip/ip/prim/rtl/prim_ram_1p_pkg.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/vendor/lowrisc_ip/ip/prim_generic/rtl/prim_generic_buf.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/vendor/lowrisc_ip/ip/prim_generic/rtl/prim_generic_clock_gating.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/dv/uvm/core_ibex/common/prim/prim_buf.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/dv/uvm/core_ibex/common/prim/prim_pkg.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/dv/uvm/core_ibex/common/prim/prim_clock_gating.sv
analyze -sv12 +define+SYNTHESIS -incdir $prim -incdir $dv $ibex_root/rtl/ibex_top.sv

analyze -sv12 -incdir $sail_lib_dir build/ibexspec.sv
analyze -sv12 spec/stub.sv

analyze -sv12 spec/spec_api.sv

# analyze -sv12 bound/binder.sv
# analyze -sv12 bound/if.sv
analyze -sv12 check/peek/alt_lsu.sv

analyze -sv12 check/top.sv

elaborate -top top -disable_auto_bbox
clock clk_i
reset ~rst_ni

set_proofgrid_max_local_jobs 10
set_proofgrid_per_engine_max_local_jobs 8

# AMcustom1
custom_engine -add -code hT3N1rhP11/52HrFRS21ROp2LOjVTgPvT8L8BGXHgLhaIuqtT4nARFjUqrBL+7pLmaTOzBepZW/Jm8SSrHDybSQtoNiO3y43wk+dEoWlsZizu97Fih6O6lPVG/LpWP5SsUPwlGagLNa1FKEFvwVXyX7//8prySbvSxIHXr5er+z4RAEA

# AMcustom2
custom_engine -add -code hT3Ng7hP/feYQOTDZ3qhYOwGAM51eA+J/FjkM5shLioAsqhgLR4Ft+O1BuKG6ilQ83B9tLXSmmqwm7g9AQA

# Ncustom3
custom_engine -add -code hT3OXrhPByJp3TrFSTLhUmMH4KVtJgmTCnNDF46yMXOKY48m4LS5nE7yBzFjA7kDuwO/GhGUpEPiky3p3wmPn3dJZHxFMsafSoObRzSC+tn7sEY0WbTdZ/FV4hL3MYH/b1CIUvXSWR4wqEoVLsmMOD4xIPT4lI1LO6ZCO7PnnWQuLwetnvKlrXx6wCW/A+x+enqslg1YPobi4wEF/EvbzOvcTYdJvl2s4H2yZg2b2ofAVN5WvhWk1HoBAA

# ADcustom4
custom_engine -add -code hT3Nv7hPv1752HrFRa2kROx2f/ECJeZB2AZsLdlO8VwmIuqtT4nIDFXclhg+O+o+DMmQCekbheGk0kK28laA9gaOFDXsQp29J3X615HY1IPHJWd6FUFvCHjO+p1k652b5JJvZlShNpGlGSXAiQe/mEAj6tEBAA

# Ncustom5
custom_engine -add -code hT3Ng7hPPfiYQOTDZ3qhYOwGAM51eA+J/FjkM5shLioAsqhgLR4Ft+O1BuKG6ilQ83B9tLXSl+CwjiTMAQA

# Mpcustom6
custom_engine -add -code hT3NZbhP9fmY2AbBQnsjfOxn6c+6e6yL+/e8fZFmaQrnlgEA

# prove -bg -all -covers

proc enter_stopat {} {
	stopat -reset {*}
}

proc exit_stopat {} {
	stopat -reset -clear
}

proc assume_mtypes {} {
	assume -from_assert {Step10::top.MType_*_Data}
}

proc prove_lemmas {} {
	assume_mtypes

	prove -task Step0
	report -task Step0

	prove -task Step1
	report -task Step1

	prove -task Step2
	report -task Step2

	prove -task Step3
	report -task Step3

	prove -task Step4
	report -task Step4

	prove -task Step5
	report -task Step5

	prove -property Step6::top.Ibex_FetchErrRoot
	prove -property {Step6::top.Ibex_SpecStableLoad Step6::top.Ibex_SpecStableLoadSnd Step6::top.Ibex_SpecStableLoadAddr Step6::top.Ibex_SpecStableLoadSndAddr Step6::top.Ibex_SpecStableStore Step6::top.Ibex_SpecStableStoreSnd Step6::top.Ibex_SpecStableStoreAddr Step6::top.Ibex_SpecStableStoreSndAddr Step6::top.Ibex_SpecStableStoreData Step6::top.Ibex_SpecStableStoreSndData} -engine_mode Hp
	prove -task Step6
	report -task Step6

	prove -task Step7
	report -task Step7

	prove -task Step8
	report -task Step8

	prove -property {Step9::top.Arith_I_Fast Step9::top.Arith_R_Fast Step9::top.Arith_Shift_Fast Step9::top.CSR_Fast Step9::top.BType_FinishFirstCycle Step9::top.BType_Fast Step9::top.JType_FinishFirstCycle Step9::top.UType_Lui_Fast Step9::top.UType_Auipc_Fast Step9::top.Fence_Fence_Fast Step9::top.Fence_FenceI_Fast Step9::top.Special_ECall_Fast Step9::top.Special_EBreak_Fast Step9::top.Special_MRet_Fast Step9::top.WFI_Fast}
	prove -property {Step9::top.Mem_MemSpec_Initial Step9::top.Mem_MemSpec_Initial_IdleActive Step9::top.Mem_MemSpec_WaitRvalidMis_Step Step9::top.Mem_MemSpec_WaitRvalidMis_WaitRvalidMis_Inv Step9::top.Mem_MemSpec_WaitRvalidMis_WaitRvalidMisGntsDone_Inv Step9::top.Mem_MemSpec_WaitRvalidMis_WaitGntSplit_Inv Step9::top.Mem_MemSpec_WaitRvalidMis_Step_Inv Step9::top.Mem_MemSpec_WaitGntSplit_Step Step9::top.Mem_MemSpec_WaitGntSplit_WaitGntSplit_Inv Step9::top.Mem_MemSpec_WaitGntSplit_Step_Inv Step9::top.Mem_MemSpec_WaitGnt_Step Step9::top.Mem_MemSpec_WaitGnt_WaitGnt_Inv Step9::top.Mem_MemSpec_WaitGnt_Step_Inv Step9::top.Mem_MemSpec_WaitRvalidMisGntsDone_Step Step9::top.Mem_MemSpec_WaitRvalidMisGntsDone_WaitRvalidMisGntsDone_Inv Step9::top.Mem_MemSpec_WaitRvalidMisGntsDone_Step_Inv Step9::top.Mem_MemSpec_IdleActive_Step Step9::top.Mem_MemSpec_IdleActive_WaitRvalidMis_Inv Step9::top.Mem_MemSpec_IdleActive_WaitGntMis_Inv Step9::top.Mem_MemSpec_IdleActive_WaitGnt_Inv Step9::top.Mem_MemSpec_IdleActive_Step_Inv Step9::top.Mem_MemSpec_WaitGntMis_Step Step9::top.Mem_MemSpec_WaitGntMis_WaitGntMis_Inv Step9::top.Mem_MemSpec_WaitGntMis_WaitRvalidMis_Inv}
	prove -property {Step9::top.IRQ_PC Step9::top.IRQ_CSR}
	prove -property {Step9::top.Illegal_Fast Step9::top.FetchErr_Fast}
	prove -task Step9
	report -task Step9

	prove -property {Step10::top.Arith_I_NoErr Step10::top.Arith_R_NoErr Step10::top.Arith_Shift_NoErr Step10::top.CSR_Addr_NotErr Step10::top.CSR_Data_NotErr Step10::top.CSR_CSR_NotErr Step10::top.CSR_PC_NotErr Step10::top.CSR_Addr_Err Step10::top.CSR_Data_Err Step10::top.CSR_CSR_Err Step10::top.CSR_PC_Err}
	prove -property {Step10::top.BType_BInd_Initial Step10::top.BType_BInd_Initial_Stall Step10::top.BType_BInd_Initial_Oma Step10::top.BType_BInd_Initial_Progress Step10::top.BType_BInd_Stall_Step Step10::top.BType_BInd_Stall_Stall_Inv Step10::top.BType_BInd_Stall_Progress_Inv Step10::top.BType_BInd_Oma_Step_0 Step10::top.BType_BInd_Oma_Oma_Inv_0 Step10::top.BType_BInd_Oma_Progress_Inv_0 Step10::top.BType_BInd_Oma_Step_1 Step10::top.BType_BInd_Oma_Oma_Inv_1 Step10::top.BType_BInd_Oma_Progress_Inv_1}
	prove -property {Step10::top.JType_JInd_Initial Step10::top.JType_JInd_Initial_Stall Step10::top.JType_JInd_Initial_Oma Step10::top.JType_JInd_Initial_Progress Step10::top.JType_JInd_Stall_Step Step10::top.JType_JInd_Stall_Stall_Inv Step10::top.JType_JInd_Stall_Progress_Inv Step10::top.JType_JInd_Oma_Step Step10::top.JType_JInd_Oma_Oma_Inv Step10::top.JType_JInd_Oma_Progress_Inv}
	prove -property {Step10::top.UType_Lui_Addr Step10::top.UType_Lui_Data Step10::top.UType_Lui_CSR Step10::top.UType_Lui_PC Step10::top.UType_Auipc_Addr Step10::top.UType_Auipc_Data Step10::top.UType_Auipc_CSR Step10::top.UType_Auipc_PC}
	prove -property {Step10::top.Fence_Fence_Addr Step10::top.Fence_Fence_Data Step10::top.Fence_Fence_CSR Step10::top.Fence_Fence_PC Step10::top.Fence_FenceI_Addr Step10::top.Fence_FenceI_Data Step10::top.Fence_FenceI_CSR Step10::top.Fence_FenceI_PC}
	prove -property {Step10::top.Special_ECall_Addr Step10::top.Special_ECall_Data Step10::top.Special_ECall_CSR Step10::top.Special_ECall_PC Step10::top.Special_EBreak_Addr Step10::top.Special_EBreak_Data Step10::top.Special_EBreak_CSR Step10::top.Special_EBreak_PC Step10::top.Special_MRet_Addr Step10::top.Special_MRet_Data Step10::top.Special_MRet_CSR Step10::top.Special_MRet_PC}
	prove -property {Step10::top.WFI_Addr_NotErr Step10::top.WFI_Data_NotErr Step10::top.WFI_PC_NotErr Step10::top.WFI_CSR_NotErr}
	prove -property {Step10::top.WFI_Addr_Err Step10::top.WFI_Data_Err Step10::top.WFI_PC_Err Step10::top.WFI_CSR_Err}
	prove -property {Step10::top.Mem_MemSpec_IdleActive_Rev Step10::top.Mem_MemSpec_WaitGntMis_Rev Step10::top.Mem_MemSpec_WaitRvalidMis_Rev Step10::top.Mem_MemSpec_WaitGntSplit_Rev Step10::top.Mem_MemSpec_WaitGnt_Rev Step10::top.Mem_MemSpec_WaitRvalidMisGntsDone_Rev Step10::top.Mem_MemSpec_Step_Rev}
	prove -property {Step10::top.Illegal_Addr Step10::top.Illegal_Data Step10::top.Illegal_PC Step10::top.Illegal_CSR}
	prove -property {Step10::top.FetchErr_Addr Step10::top.FetchErr_Data Step10::top.FetchErr_PC Step10::top.FetchErr_CSR}
	prove -property {Step10::top.MType_Mul_Addr Step10::top.MType_Mul_CSR Step10::top.MType_Mul_PC Step10::top.MType_MulH_Addr Step10::top.MType_MulH_CSR Step10::top.MType_MulH_PC Step10::top.MType_MulHSH_Addr Step10::top.MType_MulHSH_CSR Step10::top.MType_MulHSH_CSR Step10::top.MType_MulHSH_PC Step10::top.MType_MulHU_Addr Step10::top.MType_MulHU_CSR Step10::top.MType_MulHU_PC}
	prove -property {Step10::top.MType_Div_Addr Step10::top.MType_Div_CSR Step10::top.MType_Div_PC Step10::top.MType_DivU_Addr Step10::top.MType_DivU_CSR Step10::top.MType_DivU_PC  Step10::top.MType_Rem_Addr Step10::top.MType_Rem_CSR Step10::top.MType_Rem_PC Step10::top.MType_RemU_Addr Step10::top.MType_RemU_CSR Step10::top.MType_RemU_PC}
	prove -task Step10
	report -task Step10

	prove -property {Step11::top.Arith_I_Addr Step11::top.Arith_I_Data Step11::top.Arith_I_CSR Step11::top.Arith_I_PC}
	prove -property {Step11::top.Arith_R_Addr Step11::top.Arith_R_Data Step11::top.Arith_R_CSR Step11::top.Arith_R_PC}
	prove -property {Step11::top.Arith_Shift_Addr Step11::top.Arith_Shift_Data Step11::top.Arith_Shift_CSR Step11::top.Arith_Shift_PC}
	prove -property {Step11::top.BType_BInd_Stall_Rev Step11::top.BType_BInd_Oma_Rev_0 Step11::top.BType_BInd_Oma_Rev_1 Step11::top.BType_BInd_Progress_Rev Step11::top.JType_JInd_Progress_Rev Step11::top.JType_JInd_Stall_Rev Step11::top.JType_JInd_Oma_Rev}
	prove -property {Step11::top.Mem_MemSpec_IdleActive Step11::top.Mem_MemSpec_WaitGntMis Step11::top.Mem_MemSpec_WaitRvalidMis Step11::top.Mem_MemSpec_WaitGntSplit Step11::top.Mem_MemSpec_WaitGnt Step11::top.Mem_MemSpec_WaitRvalidMisGntsDone Step11::top.Mem_MemSpec_Step}
	prove -task Step11
	report -task Step11

	prove -task Step12
	report -task Step12

	prove -task Step13
	report -task Step13

	prove -task Step14
	report -task Step14

	prove -task Step15
	report -task Step15

	prove -task Step16
	report -task Step16

	prove -task Step17
	report -task Step17

	prove -task Step18
	report -task Step18

	prove -property {Step19::top.Mem_L_*_Err}
	prove -property {Step19::top.Mem_L_*_NoErr}
	prove -property {Step19::top.Mem_L_*}
	prove -property {Step19::top.Mem_S_*_Err}
	prove -property {Step19::top.Mem_S_*_NoErr}
	prove -property {Step19::top.Mem_S_*}
	prove -task Step19
	report -task Step19
}

proc prove_no_liveness {} {
	prove_lemmas

	prove -task Step20
	report -task Step20

	prove -task Step21 -engine_mode D
	report -task Step21

	prove -task Step22
	report -task Step22

	prove -task Step23
	report -task Step23
}

# TODO fix step numbers in here
proc prove_liveness {} {
	prove_lemmas

	prove -property {Step18::top.Liveness_*}
	prove -task Step18
	report -task Step18

	prove -property Step19::top.Liveness_DivStart
	prove -property Step19::top.Liveness_DivMiddle
	prove -property Step19::top.Liveness_DivEnd
	prove -property Step19::top.Liveness_WFIStart
	prove -property Step19::top.Liveness_WFIMiddle
	prove -property Step19::top.Liveness_WFIEnd
	prove -property Step19::top.Liveness_NewProgNormal
	prove -property Step19::top.Liveness_NewProgMem
	prove -property Step19::top.Liveness_ProgReadyNormal
	prove -property Step19::top.Liveness_ProgReadyWFI
	prove -property Step19::top.Liveness_KillReady
	prove -property Step19::top.Liveness_ReadyNew
	prove -property Step19::top.Liveness_Initial
	prove -property Step19::top.Liveness_FlushedNoKill
	prove -task Step19
	report -task Step19

	prove -task Step20
	report -task Step20

	prove -task Step21
	report -task Step21

	prove -task Step22
	report -task Step22

	prove -task Step23
	report -task Step23

	prove -task Step24
	report -task Step24

	prove -task Step25
	report -task Step25

	prove -task Step26
	report -task Step26

	prove -task Step27
	report -task Step27

	prove -task Step28
	report -task Step28

	prove -task Step29
	report -task Step29

	prove -property Step30::top.Live
	prove -task Step30 -engine_mode D
	report -task Step30
}

source build/psgen.tcl
