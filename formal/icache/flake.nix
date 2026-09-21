# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
{
  description = "ibex_icache JasperGold formal check";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";

  outputs = { self, nixpkgs }: let
    system = "x86_64-linux";
    pkgs = nixpkgs.legacyPackages.${system};
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
      formal = formalShell;
      default = formalShell;
    };
  };
}