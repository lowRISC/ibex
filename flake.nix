{
  description = "Environment for developing and simulating the ibex core.";

  inputs = {
    # The input 'lowrisc-nix' contains some common dependencies that can be used
    # by lowRISC projects. There is also an associated public binary cache.
    lowrisc-nix.url = "github:lowRISC/lowrisc-nix";
    # The input 'lowrisc-nix-private' is access-controlled.
    # Outputs which depend on this input are for internal use only, and will fail
    # to evaluate without the appropriate credentials.
    # All outputs which depend on this input are suffixed '_lowrisc'
    lowrisc-nix-private.url = "git+ssh://git@github.com/lowRISC/lowrisc-nix-private.git";

    nixpkgs.follows = "lowrisc-nix/nixpkgs";
    flake-utils.follows = "lowrisc-nix/flake-utils";
    poetry2nix.follows = "lowrisc-nix/poetry2nix";
    sv2v = {
      url = "github:zachjs/sv2v";
      flake = false;
    };
  };

  outputs = inputs: let

    # Only tested with the following systems:
    # - x86_64-linux
    system = inputs.flake-utils.lib.system.x86_64-linux;

    pkgs = import inputs.nixpkgs {
      inherit system;
      config = {
        allowUnfree = true;
        allowBroken = true; # sv2v marked as broken.
      };
    };

    # This import creates internal-use only outputs, which build on
    # input attributes that cannot be fetched without appropriate credentials.
    lr = import ./nix/lowrisc.nix {
      inherit inputs pkgs system;
      extraDependencies = sim_shared_lib_deps;
    };

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

    # This shell uses mkShellNoCC as the stdenv CC can interfere with EDA tools.
    eda_shell = pkgs.lib.makeOverridable pkgs.mkShellNoCC {
      name = "ibex-devshell-eda";
      buildInputs = ibex_runtime_deps;
      nativeBuildInputs = ibex_project_deps;
      shellHook = ''
        ${ibex_profile_common}
      '';
    };

    syn_shell = shell.override (prev: {
      name = "ibex-devshell-synthesis";
      nativeBuildInputs = prev.nativeBuildInputs ++ ibex_syn.deps;
      shellHook = prev.shellHook + ibex_syn.profile;
    });

  in {
    devShells.${system} = {
      default = inputs.self.devShells.${system}.shell;
      inherit shell;
      inherit eda_shell;
      inherit syn_shell;
    } // lr.devShells;
  };
}
