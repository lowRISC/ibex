# Copyright lowRISC Contributors.
# Licensed under the MIT License, see LICENSE for details.
# SPDX-License-Identifier: MIT
{
  inputs,
  pkgs,
  ...
}: let

  python = pkgs.python312;

  # Load a uv workspace from a workspace root.
  workspace = inputs.uv2nix.lib.workspace.loadWorkspace { workspaceRoot = ./.; };

  # Create package overlay from workspace.
  uvLockedOverlay = workspace.mkPyprojectOverlay {
    sourcePreference = "wheel"; # "sdist";
  };

  # Construct package set from uv.lock
  pythonSet' =
    # Use base package set from pyproject.nix builders
    (pkgs.callPackage inputs.pyproject-nix.build.packages { inherit python; }).overrideScope uvLockedOverlay;

  # Apply overlay(s) to fix any build issues
  pythonSet =
    pythonSet'.pythonPkgsHostHost.overrideScope
      (
        pkgs.lib.composeManyExtensions [
          inputs.pyproject-build-systems.overlays.default
          (inputs.uv2nix_hammer_overrides.overrides pkgs)
        ]
      );

  virtualenv = pythonSet.mkVirtualEnv "env" workspace.deps.default;
  virtualenv-dev = pythonSet.mkVirtualEnv "env-dev" workspace.deps.all; # include dev-dependencies

in
   virtualenv
