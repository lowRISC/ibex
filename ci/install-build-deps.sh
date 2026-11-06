#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Install development build dependencies for different Linux distributions
#

set -e

[ -f /etc/os-release ] || (echo "/etc/os-release doesn't exist."; exit 1)
. /etc/os-release

[ -n "$VERILATOR_VERSION" ] || (echo "VERILATOR_VERSION must be set."; exit 1)
[ -n "$VERIBLE_VERSION" ] || (echo "VERIBLE_VERSION must be set."; exit 1)
[ -n "$RISCV_TOOLCHAIN_TAR_VERSION" ] || (echo "RISCV_TOOLCHAIN_TAR_VERSION must be set."; exit 1)
[ -n "$RISCV_TOOLCHAIN_TAR_VARIANT" ] || (echo "RISCV_TOOLCHAIN_TAR_VARIANT must be set."; exit 1)
[ -n "$RISCV_GCC_LIBGCC_TAR_VERSION" ] || (echo "RISCV_GCC_LIBGCC_TAR_VERSION must be set."; exit 1)
[ -n "$RISCV_GCC_LIBGCC_TAR_VARIANT" ] || (echo "RISCV_GCC_LIBGCC_TAR_VARIANT must be set."; exit 1)

SUDO_CMD=""
if [ "$(id -u)" -ne 0 ]; then
  SUDO_CMD="sudo "
fi

if [ -z "$GITHUB_ACTIONS" ]; then
  GITHUB_PATH=/dev/null
  GITHUB_ENV=/dev/null
fi

# Use non-default mirror for Ubuntu packages, because the default mirror currently have problems.
$SUDO_CMD sed -i -E -e 's!http://(archive|security).ubuntu.com!http://europe-west2.gce.archive.ubuntu.com!g' /etc/apt/sources.list

case "$ID-$VERSION_ID" in
  ubuntu-20.04|ubuntu-22.04)
    # Curl must be available to get the repo key below.
    $SUDO_CMD apt-get update
    $SUDO_CMD apt-get install -y curl

    # Packaged dependencies
    # Install python3-yaml through apt to get a version with libyaml bindings,
    # which is significantly faster than the pure Python version.
    $SUDO_CMD apt-get install -y \
        device-tree-compiler \
        python3 \
        python3-pip \
        python3-setuptools \
        python3-wheel \
        python3-yaml \
        python3-dev \
        srecord \
        zlib1g-dev \
        git \
        make \
        autoconf \
        g++ \
        flex \
        bison \
        libelf-dev \
        clang-format \
        wget \
        xz-utils \
        libcairo2-dev

    wget https://storage.googleapis.com/ibex-cosim-builds/ibex-cosim-"$IBEX_COSIM_VERSION".tar.gz
    $SUDO_CMD mkdir -p /tools/riscv-isa-sim
    $SUDO_CMD chmod 777 /tools/riscv-isa-sim
    $SUDO_CMD tar -C /tools/riscv-isa-sim -xvzf ibex-cosim-"$IBEX_COSIM_VERSION".tar.gz --strip-components=1
    echo "/tools/riscv-isa-sim/bin" >> $GITHUB_PATH

    wget https://storage.googleapis.com/verilator-builds/verilator-"$VERILATOR_VERSION".tar.gz
    $SUDO_CMD mkdir -p /tools/verilator
    $SUDO_CMD chmod 777 /tools/verilator
    $SUDO_CMD tar -C /tools/verilator -xvzf verilator-"$VERILATOR_VERSION".tar.gz
    echo "/tools/verilator/$VERILATOR_VERSION/bin" >> $GITHUB_PATH
    # Python dependencies
    #
    # Updating pip and setuptools is required to have these tools properly
    # parse Python-version metadata, which some packages uses to specify that
    # an older version of a package must be used for a certain Python version.
    # If that information is not read, pip installs the latest version, which
    # then fails to run.
    $SUDO_CMD pip3 install -U pip "setuptools<66.0.0"

    $SUDO_CMD pip3 install -r python-requirements.txt

    # Install Verible
    mkdir -p build/verible
    cd build/verible
    VERIBLE_URL="https://github.com/chipsalliance/verible/releases/download/$VERIBLE_VERSION/verible-$VERIBLE_VERSION-linux-static-x86_64.tar.gz"
    $SUDO_CMD mkdir -p /tools/verible
    curl -sSfL "$VERIBLE_URL" | $SUDO_CMD tar -C /tools/verible -xvzf - --strip-components=1
    # Fixup bin permission which is broken in tarball.
    $SUDO_CMD chmod 755 /tools/verible/bin
    echo "/tools/verible/bin" >> $GITHUB_PATH
    ;;

  *)
    echo Unknown distribution. Please extend this script!
    exit 1
    ;;
esac

# Install pre-compiled toolchain (for all distributions)
TOOLCHAIN_URL="https://github.com/lowRISC/lowrisc-toolchains/releases/download/$RISCV_TOOLCHAIN_TAR_VERSION/$RISCV_TOOLCHAIN_TAR_VARIANT-$RISCV_TOOLCHAIN_TAR_VERSION.tar.xz"
mkdir -p build/toolchain
curl -Ls -o build/toolchain/rv32-toolchain.tar.xz "$TOOLCHAIN_URL"
$SUDO_CMD mkdir -p /tools/riscv && $SUDO_CMD chmod 777 /tools/riscv
$SUDO_CMD tar -C /tools/riscv -xf build/toolchain/rv32-toolchain.tar.xz --strip-components=1
echo "/tools/riscv/bin" >> $GITHUB_PATH

# The LLVM toolchain above ships only Clang and binutils, with no bundled C
# library or compiler runtime (no newlib/libgcc/compiler-rt equivalent).
# CoreMark is the only target in this repo that isn't fully freestanding
# (it calls libm's modf() and needs soft-float division routines for its
# final MHz report), so pull in the old GCC toolchain (headers, newlib and
# libgcc) to satisfy that at compile/link time. It's never invoked as a
# compiler.
LIBGCC_TOOLCHAIN_URL="https://github.com/lowRISC/lowrisc-toolchains/releases/download/$RISCV_GCC_LIBGCC_TAR_VERSION/$RISCV_GCC_LIBGCC_TAR_VARIANT-$RISCV_GCC_LIBGCC_TAR_VERSION.tar.xz"
curl -Ls -o build/toolchain/rv32-gcc-libgcc.tar.xz "$LIBGCC_TOOLCHAIN_URL"
$SUDO_CMD mkdir -p /tools/riscv-gcc-libgcc && $SUDO_CMD chmod 777 /tools/riscv-gcc-libgcc
$SUDO_CMD tar -C /tools/riscv-gcc-libgcc -xf build/toolchain/rv32-gcc-libgcc.tar.xz --strip-components=1
echo "RISCV_OLD_TOOLCHAIN_DIR=/tools/riscv-gcc-libgcc" >> $GITHUB_ENV
RISCV_LIBGCC_DIR="$(dirname "$(find /tools/riscv-gcc-libgcc/lib/gcc/riscv32-unknown-elf -name libgcc.a)")"
echo "RISCV_LIBGCC_DIR=$RISCV_LIBGCC_DIR" >> $GITHUB_ENV
