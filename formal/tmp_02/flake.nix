# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Standalone nix flake for the ibex_branch_predict formal check.
# Only requirement beyond nix is Cadence JasperGold (jg) on PATH.
#
# Usage:
#   nix develop .#formal   # enter the shell (mirrors ibex's .#formal name)
#   nix develop            # same — default shell is an alias for .#formal
#   make batch             # run the proof headlessly
#   make gui               # open JasperGold GUI

{
  description = "ibex_branch_predict JasperGold formal check";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";

  outputs = { self, nixpkgs }: let
    system = "x86_64-linux";
    pkgs   = nixpkgs.legacyPackages.${system};
    # JasperGold is a proprietary Cadence tool — it cannot be provided by nix.
    # Install it separately from Cadence and ensure `jg` is on your PATH.
    formalShell = pkgs.mkShellNoCC {
      packages = with pkgs; [ gnumake ];
      shellHook = ''
        if ! command -v jg &>/dev/null; then
          echo "ERROR: JasperGold (jg) not found on PATH."
          echo "       Obtain and install Cadence JasperGold, then ensure jg is on PATH."
          exit 1
        fi
      '';
    };
  in {
    devShells.${system} = {
      formal  = formalShell;
      default = formalShell;
    };
  };
}
