# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
{
  description = "Nix Flake for Ibex development and testing.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";

    pyproject-nix = {
      url = "github:pyproject-nix/pyproject.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    uv2nix = {
      url = "github:pyproject-nix/uv2nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.pyproject-nix.follows = "pyproject-nix";
    };
    pyproject-build-systems = {
      url = "github:pyproject-nix/build-system-pkgs";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.pyproject-nix.follows = "pyproject-nix";
      inputs.uv2nix.follows = "uv2nix";
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
      url = "github:lowrisc/sail?ref=ast_translate";
      flake = false;
    };
    lowrisc_sail_riscv = {
      url = "github:lowrisc/sail-riscv?ref=81a266b6f65365b34180af7b91708265da653878";
      flake = false;
    };
    lowrisc_yosys_slang = {
      url = "https://github.com/mndstrmr/yosys-slang";
      ref = "formal";
      flake = false;
      type = "git";
      submodules = true;
    };

    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
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
        aarch64-darwin
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

        # lowRISC fork of the yosys slang frontend.
        lowrisc_yosys_slang = import ./nix/lowrisc_yosys_slang.nix {
          inherit pkgs;
          src = inputs.lowrisc_yosys_slang;
        };

        # Create a python package set suitable for the formal flow
        # - The file dv/formal/pyproject.toml defines the package set for this environment
        # - Using the fusesoc .core files in this repo requires a lowrisc-fork of fusesoc, so this
        #   file specifies the forked repository. Most other python package dependencies are in
        #   support of fusesoc.
        formal_python_env = let
          workspace = inputs.uv2nix.lib.workspace.loadWorkspace {
            workspaceRoot = ./dv/formal;
          };
          overlay = workspace.mkPyprojectOverlay {
            sourcePreference = "wheel";
          };
          pythonSet =
            (pkgs.callPackage inputs.pyproject-nix.build.packages {
              python = pkgs.python3;
            }).overrideScope (
              lib.composeManyExtensions [
                inputs.pyproject-build-systems.overlays.default
                overlay
                (inputs.lowrisc-nix.lib.pyprojectOverrides {
                  inherit pkgs;
                })
              ]
          );
        in
          pythonSet.mkVirtualEnv "ibex-env" workspace.deps.default;

        # rIC3 needs a nightly toolchain
        toolchain = inputs.fenix.packages.${system}.toolchainOf {
          channel = "nightly";
          date = "2025-07-29";
          sha256 = "sha256-6D2b7glWC3jpbIGCq6Ta59lGCKN9sTexhgixH4Y7Nng=";
        };
        rustPlatform = pkgs.makeRustPlatform {
          inherit (toolchain) rustc cargo;
        };
        ric3_src = pkgs.fetchCrate {
          pname = "rIC3";
          version = "1.4.1";
          sha256 = "0713ncxbnz7phcnlcb5sgrwcjf3a8iapl027lca4g0aacybsgxsq";
        };
        ric3 = rustPlatform.buildRustPackage {
          pname = "ric3";
          version = "1.4.1";
          cargoLock = {
            lockFile = "${ric3_src}/Cargo.lock";
          };
          nativeBuildInputs = with pkgs; [
            cmake
            clang
          ];
          src = ric3_src;
        };

        standard_deps = [
          inputs.psgen.packages.${system}.default
          lowrisc_sail
          formal_python_env
        ] ++ (with pkgs; [
          gnumake
          patch
        ]);
        # The formal environment has an untracked external requirement on Cadence Jasper.
        # Add a check here which will prevent launching the devShell if Jasper is not found on the user's path.
        # TODO: Is this robust? Do we want to check available features?
        check_jg = ''
          if ! command -v jg &>/dev/null; then
            echo "Jasper not found on path. Not launching devShell."
            exit 1
          fi
        '';
        exports = ''
          # The following environment variables are used by the formal build scripts to pick up the locations
          # of the external source-file dependencies.
          # The can be re-exported manually for development (see .#formal-dev)
          export LOWRISC_SAIL_SRC=${lowrisc_sail.src}
          export LOWRISC_SAIL_RISCV_SRC=${inputs.lowrisc_sail_riscv}
        '';
        dev_msg = ''
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

        in {
          packages = {
            # Export the package for the lowrisc fork of the sail compiler. This allows us
            # to re-use its build environment when using the .#formal-dev flow.
            inherit lowrisc_sail;
          };
          devShells = rec {
            formal = mkshell-minimal {
              packages = standard_deps;
              shellHook = check_jg + exports;
            };

            formal-dev = mkshell-minimal {
              packages = standard_deps;
              shellHook = check_jg + exports + dev_msg;
            };

            oss-dev = mkshell-minimal {
              packages = standard_deps ++ [
                lowrisc_yosys_slang
                ((pkgs.yosys.override (attrs: { enablePython = false; })).overrideAttrs (finalAttrs: prev: { doCheck = false; }))
              ] ++ (with pkgs; [
                gtkwave # not stricly necesssary
                ric3

                # aig-manip (maybe just build in nix anyway?)
                toolchain.cargo
                toolchain.rustc
                cmake
                clang

                # yosys-config
                gcc
              ]);
              shellHook = exports + dev_msg + ''
                export LOWRISC_YOSYS_SLANG=${lowrisc_yosys_slang.out}/lib/slang.so
                export LD_LIBRARY_PATH=${pkgs.stdenv.cc.cc.lib}/lib/ # for rIC3, not sure why this should be necessary though
              '';
            };
        };
      }
  );
}
