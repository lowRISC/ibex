# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Docker container containing various hardware and software development tools
# for Ibex.

# Global configuration options.
ARG VERILATOR_VERSION=4.210
# The RISCV toolchain version should match the release tag used in GitHub.
ARG RISCV_TOOLCHAIN_TAR_VERSION=20220210-1
# This should match the version in ci/install-package-dependencies.sh
ARG GCC_VERSION=9

# Main container image.
FROM ubuntu:20.04 AS ibex
ARG VERILATOR_VERSION
ARG RISCV_TOOLCHAIN_TAR_VERSION
ARG GCC_VERSION

LABEL version="0.1"
LABEL description="Ibex development container."
LABEL maintainer="ibex@lowrisc.org"

# Use bash as default shell.
RUN ln -sf /bin/bash /bin/sh

# Add OBS repository to apt sources.
RUN OBS_URL="https://download.opensuse.org/repositories"; \
    OBS_PATH="/home:/phiwag:/edatools/xUbuntu_20.04"; \
    REPO_URL="${OBS_URL}${OBS_PATH}"; \
    \
    EDATOOLS_REPO_KEY="${REPO_URL}/Release.key"; \
    EDATOOLS_REPO="deb ${REPO_URL}/ /"; \
    \
    apt-get update && \
    apt-get install -y curl && \
    \
    curl -f -sL -o "$TMPDIR/obs.asc" "$EDATOOLS_REPO_KEY" || { \
        error "Failed to download repository key from ${REPO_URL}"; \
    } && \
    echo "$EDATOOLS_REPO" > "$TMPDIR/obs.list" && \
    mv "$TMPDIR/obs.asc"  /etc/apt/trusted.gpg.d/obs.asc && \
    mv "$TMPDIR/obs.list" /etc/apt/sources.list.d/edatools.list

# Install system packages
#
# Install (and cleanup) required packages (from apt-requirements.txt).
# Also add some additional packages for the use within this container and for
# developer convenience:
# - gosu and sudo are used by the scripting to make the image more convenient
#   to use.
# - locales and locales-all are required to set the locale.
# - minicom and screen are useful to see UART communication.
# - dc and time are requirements of Synopsys VCS.
# - csh and ksh are requirements of Cadence Xcelium.
# - software-properties-common is required to be able to install newer gcc versions.

# Necessary to avoid user interaction with tzdata during install
ARG DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

COPY apt-requirements.txt /tmp/apt-requirements.txt
RUN echo "verilator-${VERILATOR_VERSION}" >>/tmp/apt-requirements.txt \
    && sed -i -e '/^$/d' -e '/^#/d' -e 's/#.*//' /tmp/apt-requirements.txt \
    && apt-get update \
    && xargs apt-get install -y </tmp/apt-requirements.txt \
    && DEBIAN_FRONTEND=noninteractive TZ=Etc/UTC apt-get install -y \
        sudo \
        gosu \
        locales \
        locales-all \
        minicom \
        screen \
        dc \
        time \
        software-properties-common \
        environment-modules \
        tclsh \
        csh \
        ksh \
    && apt-get clean; \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* /usr/share/doc/*

# Install the CI version of gcc and g++
RUN add-apt-repository ppa:ubuntu-toolchain-r/test \
    && apt-get update \
    && apt-get install -y gcc-${GCC_VERSION} g++-${GCC_VERSION} \
    && update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-${GCC_VERSION} 90 \
    && update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-${GCC_VERSION} 90

# RISC-V device toolchain
COPY util/get-toolchain.py /tmp/get-toolchain.py
RUN /tmp/get-toolchain.py -r ${RISCV_TOOLCHAIN_TAR_VERSION} \
    && rm -f /tmp/get-toolchain.py

# Set Locale to utf-8 everywhere
ENV LC_ALL en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en

# Scripting for use within this container.
COPY util/container/start.sh /start.sh
COPY util/container/sudoconf /etc/sudoers.d/dev

# Add the development user (UID/GID to be replaced).
RUN groupadd dev \
    && useradd --create-home -g dev dev \
    && usermod -p '*' dev \
    && passwd -u dev

# All subsequent steps are performed as user.
USER dev:dev

# Install Python plus packages.
#
# Explicitly updating pip and setuptools is required to have these tools
# properly parse Python-version metadata, which some packages uses to
# specify that an older version of a package must be used for a certain
# Python version. If that information is not read, pip installs the latest
# version, which then fails to run.
ENV PATH "/home/dev/.local/bin:${PATH}"
COPY --chown=dev:dev python-requirements.txt /tmp/python-requirements.txt
RUN sudo mkdir -p vendor/google_riscv-dv
COPY --chown=dev:dev vendor/google_riscv-dv/requirements.txt \
                     /tmp/vendor/google_riscv-dv/requirements.txt

RUN python3 -m pip install --user -U pip setuptools \
    && python3 -m pip install --user -r /tmp/python-requirements.txt \
        --no-warn-script-location \
    && rm -f /tmp/python-requirements.txt \
    && rm -rf /tmp/vendor

# Set RISC-V-specific environment variables.
ENV RISCV /tools/riscv
ENV RISCV_TOOLCHAIN "${RISCV}"
ENV RISCV_GCC "${RISCV}/bin/riscv32-unknown-elf-gcc"
ENV RISCV_OBJCOPY "${RISCV}/bin/riscv32-unknown-elf-objcopy"

# Build and install Spike.
RUN mkdir /tmp/spike && cd /tmp/spike \
    && git clone https://github.com/lowRISC/riscv-isa-sim && cd riscv-isa-sim \
    && git checkout 15fbd5680e44da699f828c67db15345822a47ef6 \
    && mkdir build && cd build \
    && ../configure --prefix=$RISCV --enable-commitlog --enable-misaligned \
    && make -j16 \
    && sudo make install
ENV SPIKE_PATH "${RISCV}/bin"
ENV PKG_CONFIG_PATH "${PKG_CONFIG_PATH}:${RISCV}/lib/pkgconfig"

USER root:root

ENTRYPOINT [ "/start.sh" ]
