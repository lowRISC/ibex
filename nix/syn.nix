# Copyright lowRISC Contributors.
# Licensed under the MIT License, see LICENSE for details.
# SPDX-License-Identifier: MIT

# Deps for Ibex synthesis jobs

{
  inputs,
  pkgs,
  ...
}: let

  sv2v_local = import ./sv2v.nix {inherit inputs pkgs;};

  ibex_syn_deps = [
    sv2v_local.default
  ] ++ (with pkgs; [
    # haskellPackages.sv2v # broken
    yosys
    openroad
  ]);

  # Create a dumb package of nangate45
  # > All we need is a path to the sources
  nangate45 = pkgs.stdenv.mkDerivation rec {
    pname = "openroad-nangate45";
    version = "PDKv1.3_v2010_12.Apache.CCL";
    src = pkgs.fetchFromGitHub {
      owner = "The-OpenROAD-Project";
      repo = "OpenROAD-flow-scripts";
      rev = "181e9133776117ea1b9f74dbacbfdaadff8c331b"; # Tag: v3.0
      hash = "sha256-fYAdhBsMcuCXmPMQVCRdm75Tk0rd9zLnLfJdjhnhC00=";
    };
    sourceRoot = "${src.name}/flow/platforms/nangate45";
    phases = [ "unpackPhase" "installPhase" ];
    installPhase = ''
        mkdir -p $out
        cp -r ./* $out
      '';
  };

  ibex_syn_profile = ''
    export LR_SYNTH_CELL_LIBRARY_NAME=nangate
    export LR_SYNTH_CELL_LIBRARY_PATH=${nangate45}/lib/NangateOpenCellLibrary_typical.lib
  '';

in {

  deps = ibex_syn_deps;
  profile = ibex_syn_profile;

}
