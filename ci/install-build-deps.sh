#!/bin/bash
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

SUDO_CMD=""
if [ "$(id -u)" -ne 0 ]; then
  SUDO_CMD="sudo "
fi

case "$ID-$VERSION_ID" in
  ubuntu-16.04|ubuntu-18.04|ubuntu-20.04)
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
        xz-utils

    wget https://storage.googleapis.com/ibex-cosim-builds/ibex-cosim-"$IBEX_COSIM_VERSION".tar.gz
    $SUDO_CMD mkdir -p /tools/riscv-isa-sim
    $SUDO_CMD chmod 777 /tools/riscv-isa-sim
    $SUDO_CMD tar -C /tools/riscv-isa-sim -xvzf ibex-cosim-"$IBEX_COSIM_VERSION".tar.gz --strip-components=1
    echo "##vso[task.prependpath]/tools/riscv-isa-sim/bin"

    wget https://storage.googleapis.com/verilator-builds/verilator-"$VERILATOR_VERSION".tar.gz
    $SUDO_CMD mkdir -p /tools/verilator
    $SUDO_CMD chmod 777 /tools/verilator
    $SUDO_CMD tar -C /tools/verilator -xvzf verilator-"$VERILATOR_VERSION".tar.gz
    echo "##vso[task.prependpath]/tools/verilator/$VERILATOR_VERSION/bin"
    # Python dependencies
    #
    # Updating pip and setuptools is required to have these tools properly
    # parse Python-version metadata, which some packages uses to specify that
    # an older version of a package must be used for a certain Python version.
    # If that information is not read, pip installs the latest version, which
    # then fails to run.
    $SUDO_CMD pip3 install -U pip setuptools

    $SUDO_CMD pip3 install -r python-requirements.txt

    # Install Verible
    mkdir -p build/verible
    cd build/verible
    curl -Ls -o verible.tar.gz "https://github.com/google/verible/releases/download/$VERIBLE_VERSION/verible-$VERIBLE_VERSION-Ubuntu-$VERSION_ID-$VERSION_CODENAME-x86_64.tar.gz"
    $SUDO_CMD mkdir -p /tools/verible && $SUDO_CMD chmod 777 /tools/verible
    tar -C /tools/verible -xf verible.tar.gz --strip-components=1
    echo "##vso[task.prependpath]/tools/verible/bin"
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
tar -C /tools/riscv -xf build/toolchain/rv32-toolchain.tar.xz --strip-components=1
echo "##vso[task.prependpath]/tools/riscv/bin"
