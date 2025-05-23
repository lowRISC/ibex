# Copyright lowRISC Contributors.
# Licensed under the MIT License, see LICENSE for details.
# SPDX-License-Identifier: MIT
{pkgs, ...}:
let
  pypkgs-missing-build-requirements = {
    # package: build-requirements #
    alabaster = ["flit-core"];
    # pyboolector = ["setuptools"];
    lib-detect-testenv = ["setuptools"];
    cli-exit-tools = ["setuptools"];
    pathlib3x = ["setuptools"];
    typing-utils = ["setuptools"];
    svg-py = ["flit-core"];
    python-jsonschema-objects = ["setuptools"];
    sphinx-issues = ["setuptools"];
    sphinxcontrib-log-cabinet = ["setuptools"];
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

  preferwheel-overlay = final: prev: {
    pyboolector = prev.pyboolector.override { # missing "setuptools"
      preferWheel = true;
    };
    click = prev.click.override {
      preferWheel = true;
    };
    markdown = prev.markdown.override {
      preferWheel = true;
    };
    typing-extensions = prev.typing-extensions.override {
      preferWheel = true;
    };
    typing-inspection = prev.typing-inspection.override {
      preferWheel = true;
    };
    urllib3 = prev.urllib3.override {
      preferWheel = true;
    };
    attrs = prev.attrs.override {
      preferWheel = true;
    };
    referencing = prev.referencing.override {
      preferWheel = true;
    };
    jsonschema-specifications = prev.jsonschema-specifications.override {
      preferWheel = true;
    };
    pallets-sphinx-themes = prev.pallets-sphinx-themes.override {
      preferWheel = true;
    };
    pillow = prev.pillow.override {
      preferWheel = true;
    };
  };
in
  pkgs.lib.composeManyExtensions [
    preferwheel-overlay
    buildreqs-overlay
  ]
