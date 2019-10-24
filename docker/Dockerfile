# Dockerfile for ibex verification according to azure-pipelines.yml

# All steps not depending on tested code are performed in this Dockerfile.
# The rest is in entrypoint.sh script.

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:16.04
LABEL maintainter="Marek Pikuła <marek.pikula@sent.tech>"

ENV VERILATOR_VERSION=4.016
ENV VERILATOR_PATH=/opt/buildcache/verilator/${VERILATOR_VERSION}
ENV RISCV_TOOLCHAIN_TAR_VERSION=20190807-1

## Install dependencies
# Installing six is a workaround for pip dependency resolution: six is already
# installed as system package with a version below the required one.
# Explicitly installing six through pip gets us a supported version.
RUN apt-get update && \
      apt-get install -y python3 python3-pip python3-setuptools srecord zlib1g-dev git make autoconf g++ flex bison curl && \
      pip3 install -U six fusesoc

## Change to build user
RUN useradd -ms /bin/bash ibex
USER ibex
WORKDIR /home/ibex

## Build and install Verilator
RUN mkdir -p build/verilator
WORKDIR build/verilator
RUN curl -Ls -o verilator.tgz https://www.veripool.org/ftp/verilator-${VERILATOR_VERSION}.tgz && tar -xf verilator.tgz
WORKDIR verilator-${VERILATOR_VERSION}
RUN ./configure --prefix=${VERILATOR_PATH} && make -j4
USER root
RUN mkdir -p ${VERILATOR_PATH} && chown ibex:ibex ${VERILATOR_PATH}
USER ibex
RUN make install
ENV PATH="${VERILATOR_PATH}/bin:$PATH"

WORKDIR /home/ibex

## Get precompiled RISC-V toolchain
ENV TOOLCHAIN_URL=https://github.com/lowRISC/lowrisc-toolchains/releases/download/$RISCV_TOOLCHAIN_TAR_VERSION/lowrisc-toolchain-gcc-rv32imc-${RISCV_TOOLCHAIN_TAR_VERSION}.tar.xz
RUN mkdir -p build/toolchain
RUN curl -Ls -o build/toolchain/rv32-toolchain.tar.xz ${TOOLCHAIN_URL}
USER root
RUN mkdir -p /tools/riscv && chmod 777 /tools/riscv
USER ibex
RUN tar -C /tools/riscv -xf build/toolchain/rv32-toolchain.tar.xz --strip-components=1
ENV PATH="/tools/riscv/bin:$PATH"

## Display environment
# In entrypoint script

## Lint Verilog source files with Verilator
# In entrypoint script

## Get RISC-V Compliance test suite
WORKDIR /home/ibex/build
RUN git clone https://github.com/riscv/riscv-compliance.git

## Run RISC-V Compliance test for Ibex RV32IMC
# In entrypoint script

## Final Docker-specific declarations
VOLUME /home/ibex/repo
WORKDIR /home/ibex/repo

ADD --chown=ibex:ibex entrypoint.sh /home/ibex/entrypoint.sh
ENTRYPOINT /home/ibex/entrypoint.sh
