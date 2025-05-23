# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
{
  description = "Environment for developing and simulating the ibex core.";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";

    poetry2nix = {
      url = "github:nix-community/poetry2nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
    mkshell-minimal.url = "github:viperML/mkshell-minimal";

    lowrisc-nix = {
      url = "github:lowrisc/lowrisc-nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };

    psgen = {
      url = "github:mndstrmr/psgen";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
    lowrisc_sail = {
      url = "github:lowrisc/sail?ref=lowrisc";
      flake = false;
    };
    lowrisc_sail_riscv = {
      url = "github:lowrisc/sail-riscv?ref=81a266b6f65365b34180af7b91708265da653878";
      flake = false;
    };

    sv2v = {
      url = "github:zachjs/sv2v";
      flake = false;
    };
  };

  # The lowRISC public nix-cache contains builds of nix packages used by lowRISC, primarily coming from github:lowRISC/lowrisc-nix.
  nixConfig = {
    extra-substituters = ["https://nix-cache.lowrisc.org/public/"];
    extra-trusted-public-keys = ["nix-cache.lowrisc.org-public-1:O6JLD0yXzaJDPiQW1meVu32JIDViuaPtGDfjlOopU7o="];
  };

  outputs = inputs@{self, ...}:
    let

      # System types to support.
      supportedSystems = with inputs.flake-utils.lib.system; [
        x86_64-linux
      ];

    in inputs.flake-utils.lib.eachSystem supportedSystems (system:
      let

        pkgs = import inputs.nixpkgs {
          inherit system;
          config = {
            allowUnfree = true;
            allowBroken = true; # sv2v marked as broken.
          };
        };
        inherit (pkgs) lib;

        mkshell-minimal = inputs.mkshell-minimal pkgs;

        ################
        # DEPENDENCIES #
        ################

        # Python environment, defined in ./nix/env/pyproject.toml
        pythonEnv = import ./nix/env {inherit inputs pkgs;};

        # lowRISC fork of Spike used as a cosimulation model for Ibex Verification
        spike = inputs.lowrisc-nix.packages.${system}.spike-ibex-cosim;

        # Currently we don't build the riscv-toolchain from src, we use a github release
        # See https://github.com/lowRISC/lowrisc-nix/blob/main/pkgs/lowrisc-toolchain-gcc-rv32imcb.nix
        rv32imcb_toolchain = inputs.lowrisc-nix.packages.${system}.lowrisc-toolchain-gcc-rv32imcb;

        ibex_runtime_deps = with pkgs; [
          libelf # Used in DPI code
          zlib # Verilator run-time dep
        ];

        sim_shared_lib_deps = with pkgs; [
          elfutils
          openssl
        ];

        ibex_project_deps =
          [
            pythonEnv
            spike
            rv32imcb_toolchain
          ] ++
          sim_shared_lib_deps ++
          (with pkgs; [
            # Tools
            cmake
            pkg-config

            # Applications
            verilator
            gtkwave

            # Libraries
            srecord
          ]);

        ibex_syn = import ./nix/syn.nix {inherit inputs pkgs;};

        # lowRISC fork of the Sail repository. The SAIL -> SV flow is used to generate the reference model.
        lowrisc_sail = import ./nix/lowrisc_sail.nix {
          inherit pkgs;
          src = inputs.lowrisc_sail;
        };

        # Sail RISC-V model with changes for Ibex
        lowrisc_sail_riscv.src = (import ./nix/lowrisc_sail_riscv.nix {
          inherit pkgs;
          src = inputs.lowrisc_sail_riscv;
        }).src;


        ################
        # ENVIRONMENTS #
        ################

        # These exports are required by scripts within the Ibex DV flow.
        ibex_profile_common = ''
          export SPIKE_PATH=${spike}/bin

          export RISCV_TOOLCHAIN=${rv32imcb_toolchain}
          export RISCV_GCC=${rv32imcb_toolchain}/bin/riscv32-unknown-elf-gcc
          export RISCV_OBJCOPY=${rv32imcb_toolchain}/bin/riscv32-unknown-elf-objcopy
        '';

        shell = pkgs.lib.makeOverridable pkgs.mkShell {
          name = "ibex-devshell";
          buildInputs = ibex_runtime_deps;
          nativeBuildInputs = ibex_project_deps;
          shellHook = ''
            # Unset these environment variables provided by stdenv, as the SS makefiles will not
            # be able to discover the riscv toolchain versions otherwise.
            unset CC OBJCOPY OBJDUMP

            ${ibex_profile_common}
          '';
        };

        syn_shell = shell.override (prev: {
          name = "ibex-devshell-synthesis";
          nativeBuildInputs = prev.nativeBuildInputs ++ ibex_syn.deps;
          shellHook = prev.shellHook + ibex_syn.profile;
        });

        # Create a python package set suitable for the formal flow
        # - The file dv/formal/pyproject.toml defines the package set for this environment
        # - Using the fusesoc .core files in this repo requires a lowrisc-fork of fusesoc, so this
        #   file specifies the forked repository. Most other python package dependencies are in
        #   support of fusesoc.
        formal_python_env = let
          poetry2nix = inputs.poetry2nix.lib.mkPoetry2Nix {inherit pkgs;};
          lowriscPoetryOverrides = inputs.lowrisc-nix.lib.poetryOverrides {inherit pkgs;};
        in
          poetry2nix.mkPoetryEnv {
            projectDir = ./dv/formal;
            overrides = [
              poetry2nix.defaultPoetryOverrides
              lowriscPoetryOverrides
            ];
          };

        in {
          packages = {
            # Export the package for the lowrisc fork of the sail compiler. This allows us
            # to re-use its build environment when using the .#formal-dev flow.
            inherit lowrisc_sail;
          };
          devShells = rec {
            inherit shell;
            inherit syn_shell;
            formal = mkshell-minimal {
              packages = [
                inputs.psgen.packages.${system}.default
                lowrisc_sail
                formal_python_env
              ] ++ (with pkgs; [
                gnumake
                patch
              ]);
              shellHook = let
                # The formal environment has an untracked external requirement on Cadence Jasper.
                # Add a check here which will prevent launching the devShell if Jasper is not found on the user's path.
                # TODO: Is this robust? Do we want to check available features?
                check_jg = ''
                  if ! command -v jg &>/dev/null; then
                    echo "Jasper not found on path. Not launching devShell."
                    exit 1
                  fi
                '';
              in ''
                ${check_jg}
                # The following environment variables are used by the formal build scripts to pick up the locations
                # of the external source-file dependencies.
                # The can be re-exported manually for development (see .#formal-dev)
                export LOWRISC_SAIL_SRC=${lowrisc_sail.src}
                export LOWRISC_SAIL_RISCV_SRC=${lowrisc_sail_riscv.src}
              '';
            };

            formal-dev = formal.overrideAttrs (prev: {
              shellHook = prev.shellHook + ''
                cat << EOF
                ========================================================================================
                This is the development shell. By default it is identical to the .#formal shell.
                In order to use dev dependencies (e.g. psgen or Sail), prepend the new binaries to PATH:
                  export PATH=<bindir>:\$PATH
                If developing the Sail sources, also update LOWRISC_SAIL_SRC:
                  export LOWRISC_SAIL_SRC=<dirname>
                To use a local version of Ibex's sail-riscv model, also update LOWRISC_SAIL_RISCV_SRC:
                  export LOWRISC_SAIL_RISCV_SRC=<dirname>
                ========================================================================================
                EOF
              '';
            });
          };
        }
    );
}
