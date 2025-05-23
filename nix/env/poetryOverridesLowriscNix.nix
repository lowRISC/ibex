# Copyright lowRISC Contributors.
# Licensed under the MIT License, see LICENSE for details.
# SPDX-License-Identifier: MIT
{pkgs, ...}: let
  # https://github.com/nix-community/poetry2nix/blob/master/docs/edgecases.md
  # poetry2nix tries to build the python packages based on the information
  # given in their own build description files (setup.py etc.)
  # Sometimes, the inputs are incomplete. Add missing inputs here.
  pypkgs-missing-build-requirements = {
    # package: build-requirements #
    attrs = ["hatchling" "hatch-fancy-pypi-readme" "hatch-vcs"];
    beautifulsoup4 = ["hatchling"];
    pyfinite = ["setuptools"];
    zipfile2 = ["setuptools"];
    okonomiyaki = ["setuptools"];
    simplesat = ["setuptools"];
    urllib3 = ["hatchling"];
    fusesoc = ["setuptools" "setuptools-scm"];
    chipwhisperer = ["setuptools"];
    siphash = ["setuptools"];
    tockloader = ["setuptools"];
    numpy = ["distutils"];
  };
  buildreqs-overlay = (
    final: prev:
      builtins.mapAttrs (
        package: build-requirements:
          (builtins.getAttr package prev).overridePythonAttrs (old: {
            buildInputs =
              (old.buildInputs or [])
              ++ (
                builtins.map
                (pkg: builtins.getAttr pkg final)
                build-requirements
              );
          })
      )
      pypkgs-missing-build-requirements
  );

  # The following modules are very slow to build or are otherwise broken.
  # For now, preferWheel to pull the binary dist.
  preferwheel-overlay = final: prev: {
    mypy = prev.mypy.override {
      # Very slow build.
      preferWheel = true;
    };
    libcst = prev.libcst.override {
      preferWheel = true;
      #  }).overridePythonAttrs ( old: {
      #      # This fix is incomplete, and appears to be due to the issue here:
      #      # https://github.com/nix-community/poetry2nix/issues/413
      #      # https://github.com/nix-community/poetry2nix/issues/442
      #      buildInputs = (old.buildInputs or []) ++ [
      #        pkgs.rustc
      #        pkgs.cargo
      #        # pkgs.rustPlatform.cargoSetupHook
      #        final.setuptools-rust
      #      ];
      #    });
    };
    # isort = prev.isort.override {
    #   # Some problem building due to a malformed semantic version string.
    #   preferWheel = true;
    # };
    # ninja = prev.ninja.override {
    #   # Build error.
    #   preferWheel = true;
    # };
    pyyaml = prev.pyyaml.override {
      # Build error.
      preferWheel = true;
    };
  };

  # Nix wraps python programs which causes PATH to change. We want to keep
  # PATH in case a program needs to invoke user-defined programs.
  dontwrap-overlay = final: prev: {
    fusesoc = prev.fusesoc.overridePythonAttrs {
      dontWrapPythonPrograms = true;
    };
  };
in
  pkgs.lib.composeManyExtensions [
    preferwheel-overlay
    buildreqs-overlay
    dontwrap-overlay
  ]
