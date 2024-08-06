# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
{
  description = "Nix Flake for Ibex development and testing.";

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
        };
        inherit (pkgs) lib;

        mkshell-minimal = inputs.mkshell-minimal pkgs;

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
