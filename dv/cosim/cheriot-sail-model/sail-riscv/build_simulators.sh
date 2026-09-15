#!/bin/bash

function test_build () {
    declare -i rc=0
    eval $*
    rc=$?
    if [ $rc -ne 0 ]; then
        echo "Failure to execute: $*"
        exit $rc
    fi
}

test_build make ARCH=RV32 ocaml_emulator/riscv_ocaml_sim_RV32
test_build make ARCH=RV64 ocaml_emulator/riscv_ocaml_sim_RV64

test_build make ARCH=RV32 c_emulator/riscv_sim_RV32
test_build make ARCH=RV64 c_emulator/riscv_sim_RV64
