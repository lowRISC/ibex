# Copyright lowRISC Contributors.
# Licensed under the MIT License, see LICENSE for details.
# SPDX-License-Identifier: MIT

# Taken from:
# https://github.com/deemp/gists/blob/master/haskellPackage/flake.nix
# (I don't know anything about Haskell packaging.)

{
  inputs,
  pkgs,
  ...
}: let
  packageName = "sv2v";
  ghcVersion = "928";

  inherit (pkgs.haskell.lib) overrideCabal justStaticExecutables;
  hpkgs = pkgs.haskell.packages."ghc${ghcVersion}";

  # executableToolDepends - from "sv2v" expression in https://raw.githubusercontent.com/NixOS/nixpkgs/nixos-unstable/pkgs/development/haskell-modules/hackage-packages.nix
  package = overrideCabal (hpkgs.callCabal2nix packageName inputs.sv2v.outPath { })
    (x: {
      executableToolDepends = (x.executableToolDepends or [ ]) ++ (
        # Add the following extra dependencies
        with pkgs; [
          alex
          happy
        ]
      );
    });

in {
  default = justStaticExecutables package;
  inherit package;
}
