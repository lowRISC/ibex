# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
{
  description = "Nix Flake for Ibex development and testing.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    # Intentionally not following the main nixpkgs — this pin provides GCC 9.3 /
    # glibc 2.32 to build spike shared libraries with a low symbol-version floor
    # compatible with older bundled toolchains.
    nixpkgs-gcc93.url = "github:NixOS/nixpkgs/nixos-20.09";
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
    uv2nix_hammer_overrides = {
      url = "github:TyberiusPrime/uv2nix_hammer_overrides";
      inputs.nixpkgs.follows = "nixpkgs";
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

    # Deps for synthesis flows
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
        aarch64-darwin
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

        # Older nixpkgs providing GCC 9.3 / glibc 2.32, used only to compile
        # spike so the resulting .so has a low symbol-version floor compatible
        # with older bundled toolchains.
        pkgsCompat = import inputs.nixpkgs-gcc93 { inherit system; };

        mkshell-minimal = inputs.mkshell-minimal pkgs;

        ################
        # DEPENDENCIES #
        ################

        # Python environment, as defined in ./nix/pythonEnv/pyproject.toml
        pythonEnv = import ./nix/pythonEnv {inherit inputs pkgs;};

        # lowRISC fork of Spike used as a cosimulation model for Ibex Verification.
        # Built via pkgsCompat (nixos-20.09, GCC 9.3 / glibc 2.32) so the resulting
        # shared libraries carry a low symbol-version floor compatible with older
        # bundled toolchains.
        spike = pkgsCompat.spike.overrideAttrs (prev: {
          pname = "spike-ibex-cosim";
          version = "0.5-dev";
          src = pkgsCompat.fetchFromGitHub {
            owner = "lowRISC";
            repo = "riscv-isa-sim";
            rev = "4b97396656485a129119deaec2ba35e5bf354841";
            sha256 = "sha256-oF2poKMYoYXytqo/t6eqngJgrr4WFHvKj/cKsGQ88DQ=";
          };
          configureFlags = (prev.configureFlags or []) ++ ["--enable-commitlog" "--enable-misaligned"];
          # Statically embed libstdc++ and libgcc so the .so carries no
          # DT_NEEDED on libstdc++.so.6 at all.
          LDFLAGS = (prev.LDFLAGS or "") + " -static-libstdc++ -static-libgcc";
        });

        # Currently we don't build the riscv-toolchain from src, we use a github release
        # See https://github.com/lowRISC/lowrisc-nix/blob/main/pkgs/lowrisc-toolchain-gcc-rv32imcb.nix
        rv32imcb_toolchain = inputs.lowrisc-nix.packages.${system}.lowrisc-toolchain-gcc-rv32imcb;

        ibex_runtime_deps = with pkgs; [
          libelf # Used in DPI code
          zlib # Verilator run-time dep
          numactl # libnuma.so.1, required by VCS
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

            # Lints & Checking
            mypy
          ]);

        ibex_syn = import ./nix/syn.nix {inherit inputs pkgs;};

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
                (final: prev: {
                  jsonschema2md = prev.jsonschema2md.overrideAttrs (old: {
                    # Manually add babel to the build inputs
                    nativeBuildInputs = (old.nativeBuildInputs or []) ++ [ final.babel ];
                  });
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

        ################
        # ENVIRONMENTS #
        ################

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

        # This shell uses mkShellNoCC as the stdenv CC can interfere with EDA tools.
        eda_shell = pkgs.lib.makeOverridable pkgs.mkShellNoCC {
          name = "ibex-devshell-eda";
          buildInputs = ibex_runtime_deps;
          nativeBuildInputs = ibex_project_deps;
          shellHook = ''
            ${ibex_profile_common}

            # libnuma.so.1 is a bare DT_NEEDED in VCS's simv with no RPATH entry for it.
            # On NixOS there is no FHS fallback, so we must surface numactl explicitly.
            # Appending ensures the system library is preferred on FHS distros (e.g. Ubuntu).
            # zlib is also required for some waveform dumping libs.
            export LD_LIBRARY_PATH=''${LD_LIBRARY_PATH:+$LD_LIBRARY_PATH:}${pkgs.lib.makeLibraryPath [ pkgs.numactl pkgs.zlib ]}
          '';
        };

        in {
          packages = {
            # Export the package for the lowrisc fork of the sail compiler. This allows us
            # to re-use its build environment when using the .#formal-dev flow.
            inherit lowrisc_sail;
          };
          devShells = rec {
            inherit shell syn_shell eda_shell;
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
