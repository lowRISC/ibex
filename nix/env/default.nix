# Copyright lowRISC Contributors.
# Licensed under the MIT License, see LICENSE for details.
# SPDX-License-Identifier: MIT
{
  inputs,
  pkgs,
  # python3,
  ...
}: let
  poetry2nix = inputs.poetry2nix.lib.mkPoetry2Nix {inherit pkgs;};
  ibexPoetryOverrides = import ./poetryOverrides.nix {inherit pkgs;};
  lowriscPoetryOverrides = inputs.lowrisc-nix.lib.poetryOverrides {inherit pkgs;};
in
  poetry2nix.mkPoetryEnv {
    projectDir = ./.;
    overrides = [
      ibexPoetryOverrides
      lowriscPoetryOverrides
      poetry2nix.defaultPoetryOverrides
    ];
  }
