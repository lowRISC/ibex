// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A fragment of SystemVerilog code that is inserted into the ICache. We're using this to emulate
// missing bind support, so this file should do nothing but instantiate a module.
//
// Using a wildcard (.*) for ports allows the testbench to inspect internal signals of the cache.

formal_tb #(
  .BusWidth       (BusWidth),
  .CacheSizeBytes (CacheSizeBytes),
  .ICacheECC      (ICacheECC),
  .LineSize       (LineSize),
  .NumWays        (NumWays),
  .SpecRequest    (SpecRequest),
  .BranchCache    (BranchCache),

  .NUM_FB         (NUM_FB)
) tb_i (.*);
