# Copyright lowRISC Contributors.
# Licensed under the MIT License, see LICENSE for details.
# SPDX-License-Identifier: MIT
{
  inputs,
  pkgs,
  system,
  extraDependencies,
  ...
}: let

  # Proprietary EDA deps
  # These dependencies are behind the 'lowrisc-nix-private' repository, which is access-controlled.
  lowriscEdaDeps = (
    map (pkg: pkg.override {
      # The 'extraDependencies' argument can be used to add deps to the wrapped environments the
      # EDA tools run inside. Just adding the deps to the devShell environments is not sufficient, as
      # the EDA tool wrappers end up shadowing the same paths with their own wrappers, and hence cannot
      # see the additional deps.
      inherit extraDependencies;
    })
    (with inputs.lowrisc-nix-private.packages.${system}; [vcs xcelium])
  );

  lowriscProfile = ''
    # Xcelium
    # When building the simulation executable with the EDA tooling wrapped in an FHSenv, we are
    # depending on the stdenv.cc. Therefore, the appropriate shared libraries need to be
    # located at runtime for these executables to run. The rpath is not set correctly for us to
    # discover the correct libraries, and it does not appear to matter as when invoking the simulator
    # the search paths of the xrun utility are used, not those of the librun.so library.
    # However, setting the DT_NEEDED paths to be static/absolute does resolve correctly.
    # Therefore, pass the correct search paths into the build here, and patchelf the librun.so object
    # to setup DT_NEEDED correctly (in compile_tb.py) for the appropriate libs (libstdc++ / libgcc_s)
    export IBEX_NIX_SHELL_LIB=${pkgs.stdenv.cc.cc.lib}/lib
  '';

  eda_shell_lowrisc = inputs.self.devShells.${system}.eda_shell.override (prev: {
    name = "ibex-devshell-eda-lowrisc";
    nativeBuildInputs = prev.nativeBuildInputs ++ lowriscEdaDeps;
    shellHook = prev.shellHook + lowriscProfile;
  });

in rec {
  devShells = {
    inherit eda_shell_lowrisc;
  };
}
