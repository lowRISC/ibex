// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A simple "memory model" governed by a single seed
//
// We pick a contiguous PMP range that covers ~1/8 of the address space. Set
//
//    pmp_lo = seed ^ 32'hdeadbeef
//    pmp_hi = pmp_lo + min(32'd1 << (32 - 3), (~32'd0) - pmp_lo)
//
// then the disallowed PMP range will be [pmp_lo, pmp_hi].
//
// We'd like errors to be sparsely distributed in the address space, with 1/128 chance of any given
// address causing an error. We should probably do something more sensible, but for now let's XOR
// the address with something else (32'hf00dbeef) and pass it to the PMP calculation.
//
// For the memory content hash function, we use the first example from [1] (explicitly
// public-domain), except that we have 30+32 = 62 bits of input, which we just XOR together
// (aligning LSBs).
//
// [1] https://burtleburtle.net/bob/hash/integer.html

class ibex_icache_mem_model #(parameter int unsigned BusWidth = 32)
  extends uvm_object;

  protected bit [31:0] seed = 32'd0;
  protected bit        no_pmp_errs = 0;
  protected bit        no_mem_errs = 0;

  function new(string name="", bit disable_pmp_errs=0, bit disable_mem_errs=0);
    no_pmp_errs = disable_pmp_errs;
    no_mem_errs = disable_mem_errs;
  endfunction

  `uvm_object_utils_begin(ibex_icache_mem_model)
     `uvm_field_int (seed,        UVM_DEFAULT | UVM_HEX)
     `uvm_field_int (no_pmp_errs, UVM_DEFAULT)
     `uvm_field_int (no_mem_errs, UVM_DEFAULT)
  `uvm_object_utils_end

  function void set_seed(bit [31:0] new_seed);
    seed = new_seed;
  endfunction

  // Return true if reading from BusWidth bits from address should give an error
  function automatic logic is_error(logic [31:0] address);
    logic [31:0] rng_lo, rng_hi, rng_w0, rng_w1;
    rng_lo = seed ^ 32'hdeadbeef;
    rng_w0 = 32'd1 << (32 - 3);
    rng_w1 = (~32'd0) - rng_lo;
    rng_hi = rng_lo + ((rng_w0 < rng_w1) ? rng_w0 : rng_w1);

    return ranges_overlap(address, address + BusWidth / 8, rng_lo, rng_hi);
  endfunction

  // Return true iff [lo0, hi0) and [lo1, hi1) have nonempty intersection
  function automatic logic ranges_overlap(logic [31:0] lo0, logic [31:0] hi0,
                                          logic [31:0] lo1, logic [31:0] hi1);
    return (lo0 < hi1) && (lo1 < hi0);
  endfunction

  // Return true if reading BusWidth bits from address should give a PMP error
  function automatic logic is_pmp_error(logic [31:0] address);
    return (! no_pmp_errs) && is_error(address ^ 32'h12344321);
  endfunction

  // Return true if reading BusWidth bits from address should give a memory error
  function automatic logic is_mem_error(logic [31:0] address);
    return (! no_mem_errs) && is_error(address ^ 32'hf00dbeef);
  endfunction

  // Return true if reading BusWidth bits from address should give some sort of error
  function automatic logic is_either_error(logic [31:0] address);
    return is_pmp_error(address) || is_mem_error(address);
  endfunction

  // Return BusWidth bits of data from reading at address.
  function automatic logic [BusWidth-1:0] read_data(logic [31:0] address);
    logic [BusWidth-1:0] acc, word_data;
    int                  word_count, lo_idx, lo_bit;
    logic [29:0]         word_addr;

    // The number of 32-bit words we have to read is the number of words in BusWidth, plus one if
    // the address is not word-aligned.
    word_count = ((BusWidth + 31) / 32) + ((address & 32'd3) ? 1 : 0);

    // The word address of the first word we're going to read.
    word_addr = address >> 2;

    // The accumulator that we'll fill with bits of data
    acc = 0;

    // The bottom bit that should be written to this iteration
    lo_bit = 0;

    for (int i = 0; i < word_count; i++) begin
      // Note that the address sum might wrap (if we read off the top of memory), but that's not
      // really a problem.
      word_data = 0;
      word_data[31:0] = read_word(word_addr + i[29:0]);

      // The bottom valid byte in word_data is normally 0, but is positive if i is zero (the bottom)
      // word and the read was misaligned. In that case, it equals i & 3.
      lo_idx = (i > 0) ? 0 : (i & 3);

      // We don't bother tracking the top valid byte: our left shifts will just push anything extra
      // off the top anyway.
      acc = acc | (((word_data >> lo_idx) << lo_idx) << lo_bit);

      lo_bit = lo_bit + 32;
    end

    return acc;
  endfunction

  // Read 32 bits of data from reading at word_address.
  function automatic logic [31:0] read_word(logic [29:0] address);
    return hash({2'b0, address} ^ seed);
  endfunction

  // A 32-bit to 32-bit hash function (see notes at top of file)
  function automatic logic [31:0] hash(logic [31:0] in);
    in = (in ^ 32'd61) ^ (in >> 16);
    in = in + (in << 3);
    in = in ^ (in >> 4);
    in = in * 32'h27d4eb2d;
    return in ^ (in >> 15);
  endfunction

endclass
