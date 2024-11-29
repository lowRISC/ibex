#!/usr/bin/env bash
# Copyleft

# Define environment variables
MINICONDA=~/miniconda3/etc/profile.d/conda.sh
MINICONDA_ENV=ibex
# To activate this environment, use
#
#     $ conda activate ibex
#
# To deactivate an active environment, use
#
#     $ conda deactivate

# Get the root directory of the Git repository
export ROOT_DIR=$(git rev-parse --show-toplevel)

export BENDER=~/eth/bin/bender
export PULP_RISCV_GCC_TOOLCHAIN=$ROOT_DIR/install/riscv
export GCC_TOOLCHAIN=$ROOT_DIR/install/riscv-gcc/bin
export LLVM_TOOLCHAIN=$ROOT_DIR/install/riscv-llvm/bin
export CC=gcc-10
export CXX=g++-10
#
export CV_SIMULATOR=verilator
export CV_SW_TOOLCHAIN=$ROOT_DIR/install/riscv-gcc
export CV_SW_PREFIX=riscv32-unknown-elf-
export CV_SW_MARCH=rv32im_zicsr
export CV_SW_CC=gcc


source $MINICONDA
conda activate $MINICONDA_ENV

export PATH=~/eth/bin:~/verible/bin:$ROOT_DIR/install/verilator/bin:$GCC_TOOLCHAIN:$PATH
source ~/vivado.sh

echo  `verilator --version`