/*
 * Copyright 2020 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

class riscv_pmp_cfg extends uvm_object;

  // default to a single PMP region
  rand int pmp_num_regions = 1;
  // default to granularity of 0 (4 bytes grain)
  rand int pmp_granularity = 0;
  // enable bit for pmp randomization
  bit pmp_randomize = 0;
  // pmp CSR configurations
  rand pmp_cfg_reg_t pmp_cfg[];

  // used to parse addr_mode configuration from cmdline
  typedef uvm_enum_wrapper#(pmp_addr_mode_t) addr_mode_wrapper;
  pmp_addr_mode_t addr_mode;

  `uvm_object_utils_begin(riscv_pmp_cfg)
    `uvm_field_int(pmp_num_regions, UVM_DEFAULT)
    `uvm_field_int(pmp_granularity, UVM_DEFAULT)
  `uvm_object_utils_end

  // constraints
  constraint sanity_c {
    pmp_num_regions inside {[1 : 16]};
    pmp_granularity inside {[0 : XLEN + 3]};
  }

  // TODO(udinator) move these constraints to post_randomize() to save performance
  constraint xwr_c {
    foreach (pmp_cfg[i]) {
      !(pmp_cfg[i].w && !pmp_cfg[i].r);
    }
  }

  constraint grain_addr_mode_c {
    foreach (pmp_cfg[i]) {
      (pmp_granularity >= 1) -> (pmp_cfg[i].a != NA4);
    }
  }

  function new(string name = "");
    string s;
    super.new(name);
    get_bool_arg_value("+pmp_randomize=", pmp_randomize);
    pmp_cfg = new[pmp_num_regions];
    if (!pmp_randomize) begin
      set_defaults();
    end
  endfunction

  // TODO(udinator) partition address space to map to all active pmp_addr CSRs
  // TODO(udinator) set pmp address defaults
  function void set_defaults();
    foreach(pmp_cfg[i]) begin
      pmp_cfg[i].l    = 1'b0;
      pmp_cfg[i].a    = TOR;
      pmp_cfg[i].x    = 1'b1;
      pmp_cfg[i].w    = 1'b1;
      pmp_cfg[i].r    = 1'b1;
      pmp_cfg[i].addr = 34'h3FFFFFFFF;
    end
  endfunction

  function void setup_pmp();
    string pmp_region;
    get_int_arg_value("+pmp_num_regions=", pmp_num_regions);
    get_int_arg_value("+pmp_granularity=", pmp_granularity);
    // TODO(udinator) - parse the pmp configuration values
  endfunction

  // This function parses the pmp_cfg[] array to generate the actual instructions to set up
  // the PMP CSR registers.
  // Since either 4 (in rv32) or 8 (in rv64) PMP configuration registers fit into one physical
  // CSR, this function waits until it has reached this maximum to write to the physical CSR to
  // save some extraneous instructions from being performed.
  function void gen_pmp_instr(ref string instr[$], riscv_reg_t scratch_reg);
    int cfg_per_csr = XLEN / 4;
    bit [XLEN - 1 : 0] pmp_word;
    bit [XLEN - 1 : 0] cfg_bitmask;
    bit [7 : 0] cfg_byte;
    riscv_instr_pkg::privileged_reg_t base_pmp_addr = PMPADDR0;
    riscv_instr_pkg::privileged_reg_t base_pmpcfg_addr = PMPCFG0;
    int pmp_id;
    foreach (pmp_cfg[i]) begin
      // TODO(udijnator) condense this calculations if possible
      pmp_id = i / cfg_per_csr;
      cfg_byte = {pmp_cfg[i].l, pmp_cfg[i].zero, pmp_cfg[i].a,
                  pmp_cfg[i].x, pmp_cfg[i].w, pmp_cfg[i].r};
      `uvm_info(`gfn, $sformatf("cfg_byte: 0x%0x", cfg_byte), UVM_DEBUG)
      cfg_bitmask = cfg_byte << ((i % cfg_per_csr) * 8);
      `uvm_info(`gfn, $sformatf("cfg_bitmask: 0x%0x", cfg_bitmask), UVM_DEBUG)
      pmp_word = pmp_word | cfg_bitmask;
      `uvm_info(`gfn, $sformatf("pmp_word: 0x%0x", pmp_word), UVM_DEBUG)
      cfg_bitmask = 0;
      //TODO (udinator) - add rv64 support for pmpaddr writes
      instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg, pmp_cfg[i].addr[XLEN + 1 : 2]));
      instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmp_addr + i, scratch_reg));
      // short circuit if end of list
      if (i == pmp_cfg.size() - 1) begin
        instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg, pmp_word));
        instr.push_back($sformatf("csrw 0x%0x, x%0d",
                                  base_pmpcfg_addr + pmp_id,
                                  scratch_reg));
        return;
      end else if ((i + 1) % cfg_per_csr == 0) begin
        // if we've filled up pmp_word, write to the corresponding CSR
        instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg, pmp_word));
        instr.push_back($sformatf("csrw 0x%0x, x%0d",
                                  base_pmpcfg_addr + pmp_id,
                                  scratch_reg));
        pmp_word = 0;
      end
    end
  endfunction

endclass
