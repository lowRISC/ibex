// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class core_ibex_elf_manifest_test extends core_ibex_base_test;

  string elf_manifest;
  bit    use_elf_manifest = 1'b0;

  `uvm_component_utils(core_ibex_elf_manifest_test)

  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  // Copy of core_ibex_base_test::build_phase() with ELF-manifest specific input handling.
  virtual function void build_phase(uvm_phase phase);
    string cosim_log_file;
    bit [31:0] pmp_num_regions;
    bit [31:0] pmp_granularity;
    bit [31:0] mhpm_counter_num;
    bit        secure_ibex;
    bit        icache;
    bit        disable_spurious_dside_responses;

    // Check the test binary/binaries have been passed correctly
    void'($value$plusargs("bin=%0s", binary));
    void'($value$plusargs("bin_main=%0s", bin_main));
    void'($value$plusargs("bin_dm=%0s", bin_dm));
    void'($value$plusargs("vmem_main=%0s", vmem_main));
    void'($value$plusargs("vmem_dm=%0s", vmem_dm));
    void'($value$plusargs("elf_manifest=%0s", elf_manifest));

    if (elf_manifest != "") begin
      use_elf_manifest = 1'b1;
      `uvm_info(`gfn, $sformatf("Using ELF manifest: %0s", elf_manifest), UVM_LOW)
    end

    // If the 'discrete_debug_module' plusarg is set, we will have two binaries per test, one for
    // the main memory region, and one for the debug module.
    void'($value$plusargs("discrete_debug_module=%b", discrete_debug_module));
    if (!discrete_debug_module) begin
      // Single binary mode:
      // either old raw binary flow via +bin
      // or new ELF manifest flow via +elf_manifest
      if ((binary == "") && !use_elf_manifest) begin
        `uvm_fatal(`gfn,
          "Please specify either +bin=binary_name or +elf_manifest=manifest file")
      end
    end else begin
      // Discrete debug module mode, expecting two binaries passed via +bin_main and +bin_dm.
      string binaries[4] = '{bin_main, bin_dm, vmem_main, vmem_dm};
      foreach (binaries[bin]) begin
        if (binaries[bin] == "") begin
          `uvm_fatal(`gfn,
            "Specify all test binaries via plusargs +bin_main, +bin_dm, +vmem_main, +vmem_dm")
        end
      end
    end

    $value$plusargs("timeout_in_cycles=%0d", timeout_in_cycles);
    if (!uvm_config_db#(virtual clk_rst_if)::get(null, "", "clk_if", clk_vif)) begin
      `uvm_fatal(`gfn, "Cannot get clk_if")
    end
    if (!uvm_config_db#(virtual core_ibex_dut_probe_if)::get(null, "", "dut_if", dut_vif)) begin
      `uvm_fatal(`gfn, "Cannot get dut_if")
    end
    if (!uvm_config_db#(virtual core_ibex_instr_monitor_if)::get(null, "",
                                                                 "instr_monitor_if",
                                                                 instr_vif)) begin
      `uvm_fatal(`gfn, "Cannot get instr_monitor_if")
    end
    if (!uvm_config_db#(virtual core_ibex_csr_if)::get(null, "", "csr_if", csr_vif)) begin
      `uvm_fatal(`gfn, "Cannot get csr_if")
    end
    env = core_ibex_env::type_id::create("env", this);
    cfg = core_ibex_env_cfg::type_id::create("cfg", this);

    cosim_cfg = core_ibex_cosim_cfg::type_id::create("cosim_cfg", this);

    cosim_cfg.isa_string = get_isa_string();
    `uvm_info(`gfn, $sformatf("COSIM ISA = %0s", cosim_cfg.isa_string), UVM_LOW)
    cosim_cfg.start_pc    = ((32'h`BOOT_ADDR & ~(32'h0000_00FF)) | 8'h80);
    cosim_cfg.start_mtvec = ((32'h`BOOT_ADDR & ~(32'h0000_00FF)) | 8'h01);
    // TODO: Turn on when not using icache
    cosim_cfg.probe_imem_for_errs = 1'b0;
    void'($value$plusargs("cosim_log_file=%0s", cosim_log_file));
    cosim_cfg.log_file = cosim_log_file;

    if (!uvm_config_db#(bit [31:0])::get(null, "", "PMPNumRegions", pmp_num_regions)) begin
      pmp_num_regions = '0;
    end

    if (!uvm_config_db#(bit [31:0])::get(null, "", "PMPGranularity", pmp_granularity)) begin
      pmp_granularity = '0;
    end

    if (!uvm_config_db#(bit [31:0])::get(null, "", "MHPMCounterNum", mhpm_counter_num)) begin
      mhpm_counter_num = '0;
    end

    if (!uvm_config_db#(bit)::get(null, "", "SecureIbex", secure_ibex)) begin
      secure_ibex = '0;
    end

    if (!uvm_config_db#(bit)::get(null, "", "ICache", icache)) begin
      icache = '0;
    end

    cosim_cfg.pmp_num_regions   = pmp_num_regions;
    cosim_cfg.pmp_granularity   = pmp_granularity;
    cosim_cfg.mhpm_counter_num  = mhpm_counter_num;
    cosim_cfg.relax_cosim_check = cfg.disable_cosim;
    cosim_cfg.secure_ibex       = secure_ibex;
    cosim_cfg.icache            = icache;
    cosim_cfg.dm_start_addr     = 32'h`DM_ADDR;
    cosim_cfg.dm_end_addr       = 32'h`DM_ADDR + (32'h`DM_ADDR_MASK + 1);

    uvm_config_db#(core_ibex_cosim_cfg)::set(null, "*cosim_agent*", "cosim_cfg", cosim_cfg);

    imem_cfg = ibex_mem_intf_response_agent_cfg::type_id::create("imem_cfg", this);
    dmem_cfg = ibex_mem_intf_response_agent_cfg::type_id::create("dmem_cfg", this);
    // Never create bad integrity bits in response to accessing uninit memory
    // on the Iside, as the Ibex can fetch speculatively.
    imem_cfg.enable_bad_intg_on_uninit_access = 0;
    // By default, enable bad_intg on the Dside (read plusarg to overwrite this behaviour)
    dmem_cfg.enable_bad_intg_on_uninit_access = 1;
    void'($value$plusargs("enable_bad_intg_on_uninit_access=%0d",
                          dmem_cfg.enable_bad_intg_on_uninit_access));
    uvm_config_db#(ibex_mem_intf_response_agent_cfg)::
      set(this, "*instr_if_response_agent*", "cfg", imem_cfg);
    uvm_config_db#(ibex_mem_intf_response_agent_cfg)::
      set(this, "*data_if_response_agent*", "cfg", dmem_cfg);

    uvm_config_db#(core_ibex_env_cfg)::set(this, "*", "cfg", cfg);
    mem = mem_model_pkg::mem_model#()::type_id::create("mem");

    disable_spurious_dside_responses = 0;
    void'($value$plusargs("disable_spurious_dside_responses=%0d",
      disable_spurious_dside_responses));

    // Disable spurious responses for non secure configs or when disabled through plusarg
    if ((secure_ibex == 0) || disable_spurious_dside_responses) begin
      cfg.enable_spurious_dside_responses = 0;
    end

    // Create virtual sequence and assign memory handle
    vseq = core_ibex_vseq::type_id::create("vseq");
    vseq.mem = mem;
    vseq.cfg = cfg;
  endfunction

  // Copy of core_ibex_base_test::run_phase() with ELF-manifest loader branch.
  virtual task run_phase(uvm_phase phase);
    enable_irq_seq = cfg.enable_irq_single_seq || cfg.enable_irq_multiple_seq;
    phase.raise_objection(this);
    cur_run_phase = phase;

    dut_vif.dut_cb.fetch_enable <= ibex_pkg::IbexMuBiOff;
    clk_vif.wait_clks(100);

    if (use_elf_manifest) begin
      `uvm_info(`gfn,
                $sformatf("Loading ELF manifest before enabling fetch: %0s", elf_manifest),
                UVM_LOW)
      load_elf_manifest_to_mems();
    end else begin
      load_binary_to_mems();
    end

    dut_vif.dut_cb.fetch_enable <= ibex_pkg::IbexMuBiOn;

    fork
      send_stimulus();
      handle_reset();
    join_none
    wait_for_test_done();
    cur_run_phase = null;
    phase.drop_objection(this);
  endtask

  // Copy of core_ibex_base_test::handle_reset() with ELF-manifest loader branch.
  virtual task handle_reset();
    forever begin
      @(posedge dut_vif.reset);
      `uvm_info(`gfn, "Reset now active", UVM_LOW)
      // Tear-down testbench components
      // Flush FIFOs
      item_collected_port.flush();
      irq_collected_port.flush();

      @(negedge dut_vif.reset);
      `uvm_info(`gfn, "Reset now inactive", UVM_LOW)
      // Build-up testbench components

      // Cosim must be re-initialized before loading the memory
      env.reset();

      if (use_elf_manifest) begin
        load_elf_manifest_to_mems();
      end else begin
        load_binary_to_mems();
      end
    end
  endtask : handle_reset

  function void load_elf_manifest_to_mems();
    `uvm_info(`gfn,
              $sformatf("Loading ELF manifest into DUT and cosim memory: %0s", elf_manifest),
              UVM_LOW)
    load_elf_manifest_to_dut_mem(elf_manifest);
    load_elf_manifest_to_cosim_mem(elf_manifest);
  endfunction

  function void load_elf_manifest_to_dut_mem(string manifest_file);
    int        fd;
    int        r;
    string     line;
    bit [31:0] entry_addr;
    bit [31:0] seg_addr;
    bit [31:0] file_size;
    bit [31:0] mem_size;
    string     seg_flags;
    bit [7:0]  byte_val;
    bit [31:0] zero_count;
    bit [31:0] cur_addr;
    int        i;

    fd = $fopen(manifest_file, "r");
    if (!fd) begin
      `uvm_fatal(`gfn, $sformatf("Cannot open ELF manifest file %0s", manifest_file))
    end

    cur_addr = '0;

    while (!$feof(fd)) begin
      line = "";
      r = $fgets(line, fd);
      if (r == 0) begin
        `uvm_info(`gfn, "Skipping empty/failed manifest read", UVM_HIGH)
        continue;
      end

      // ENTRY,0x80000000
      if (line.len() >= 6 && line.substr(0, 5) == "ENTRY,") begin
        r = $sscanf(line, "ENTRY,0x%h", entry_addr);
        if (r != 1) begin
          `uvm_fatal(`gfn, $sformatf("Malformed ENTRY line: %0s", line))
        end
        `uvm_info(`gfn,
                  $sformatf("ELF manifest entry point = 0x%08h", entry_addr),
                  UVM_LOW)
      end

      // SEGMENT,0x80000000,0x00013f48,0x00013f48,RWX
      else if (line.len() >= 8 && line.substr(0, 7) == "SEGMENT,") begin
        r = $sscanf(line, "SEGMENT,0x%h,0x%h,0x%h,%s",
                    seg_addr, file_size, mem_size, seg_flags);
        if (r != 4) begin
          `uvm_fatal(`gfn, $sformatf("Malformed SEGMENT line: %0s", line))
        end
        cur_addr = seg_addr;
        `uvm_info(`gfn,
                  $sformatf("Loading segment: addr=0x%08h file_size=0x%08h mem_size=0x%08h flags=%0s",
                            seg_addr, file_size, mem_size, seg_flags),
                  UVM_LOW)
      end

      // SECTION,.text
      else if (line.len() >= 8 && line.substr(0, 7) == "SECTION,") begin
        `uvm_info(`gfn,
                  $sformatf("Manifest section info: %0s", line),
                  UVM_HIGH)
      end

      // BYTE,0x6f
      else if (line.len() >= 5 && line.substr(0, 4) == "BYTE,") begin
        r = $sscanf(line, "BYTE,0x%h", byte_val);
        if (r != 1) begin
          `uvm_fatal(`gfn, $sformatf("Malformed BYTE line: %0s", line))
        end
        `uvm_info(`gfn,
                  $sformatf("Init mem [0x%08h] = 0x%02h", cur_addr, byte_val),
                  UVM_FULL)
        mem.write(cur_addr, byte_val);
        cur_addr++;
      end

      // ZERO,0x00000010
      else if (line.len() >= 5 && line.substr(0, 4) == "ZERO,") begin
        r = $sscanf(line, "ZERO,0x%h", zero_count);
        if (r != 1) begin
          `uvm_fatal(`gfn, $sformatf("Malformed ZERO line: %0s", line))
        end

        `uvm_info(`gfn,
                  $sformatf("Zero-filling %0d bytes from addr 0x%08h", zero_count, cur_addr),
                  UVM_LOW)

        for (i = 0; i < zero_count; i++) begin
          mem.write(cur_addr, 8'h00);
          cur_addr++;
        end
      end

      else begin
        `uvm_fatal(`gfn, $sformatf("Unknown manifest line: %0s", line))
      end
    end

    $fclose(fd);
  endfunction

  function void load_elf_manifest_to_cosim_mem(string manifest_file);
    int        fd;
    int        r;
    string     line;
    bit [31:0] entry_addr;
    bit [31:0] seg_addr;
    bit [31:0] file_size;
    bit [31:0] mem_size;
    string     seg_flags;
    bit [7:0]  byte_val;
    bit [31:0] zero_count;
    bit [31:0] cur_addr;
    int        i;

    fd = $fopen(manifest_file, "r");
    if (!fd) begin
      `uvm_fatal(`gfn, $sformatf("Cannot open ELF manifest file %0s for cosim loading",
                                 manifest_file))
    end

    cur_addr = '0;

    while (!$feof(fd)) begin
      line = "";
      r = $fgets(line, fd);
      if (r == 0) begin
        continue;
      end

      // ENTRY,0x80000000
      if (line.len() >= 6 && line.substr(0, 5) == "ENTRY,") begin
        r = $sscanf(line, "ENTRY,0x%h", entry_addr);
        if (r != 1) begin
          `uvm_fatal(`gfn, $sformatf("Malformed ENTRY line in cosim loader: %0s", line))
        end
        `uvm_info(`gfn,
                  $sformatf("Cosim manifest entry point = 0x%08h", entry_addr),
                  UVM_LOW)
      end

      // SEGMENT,0x80000000,0x00013f48,0x00013f48,RWX
      else if (line.len() >= 8 && line.substr(0, 7) == "SEGMENT,") begin
        r = $sscanf(line, "SEGMENT,0x%h,0x%h,0x%h,%s",
                    seg_addr, file_size, mem_size, seg_flags);
        if (r != 4) begin
          `uvm_fatal(`gfn, $sformatf("Malformed SEGMENT line in cosim loader: %0s", line))
        end
        cur_addr = seg_addr;
        `uvm_info(`gfn,
                  $sformatf("Loading cosim segment: addr=0x%08h file_size=0x%08h mem_size=0x%08h flags=%0s",
                            seg_addr, file_size, mem_size, seg_flags),
                  UVM_LOW)
      end

      // SECTION,.text
      else if (line.len() >= 8 && line.substr(0, 7) == "SECTION,") begin
        `uvm_info(`gfn,
                  $sformatf("Cosim manifest section info: %0s", line),
                  UVM_HIGH)
      end

      // BYTE,0x6f
      else if (line.len() >= 5 && line.substr(0, 4) == "BYTE,") begin
        r = $sscanf(line, "BYTE,0x%h", byte_val);
        if (r != 1) begin
          `uvm_fatal(`gfn, $sformatf("Malformed BYTE line in cosim loader: %0s", line))
        end
        `uvm_info(`gfn,
                  $sformatf("Init cosim mem [0x%08h] = 0x%02h", cur_addr, byte_val),
                  UVM_FULL)
        env.cosim_agent.write_mem_byte(cur_addr, byte_val);
        cur_addr++;
      end

      // ZERO,0x00000010
      else if (line.len() >= 5 && line.substr(0, 4) == "ZERO,") begin
        r = $sscanf(line, "ZERO,0x%h", zero_count);
        if (r != 1) begin
          `uvm_fatal(`gfn, $sformatf("Malformed ZERO line in cosim loader: %0s", line))
        end

        `uvm_info(`gfn,
                  $sformatf("Cosim zero-filling %0d bytes from addr 0x%08h", zero_count, cur_addr),
                  UVM_LOW)

        for (i = 0; i < zero_count; i++) begin
          env.cosim_agent.write_mem_byte(cur_addr, 8'h00);
          cur_addr++;
        end
      end

      else begin
        `uvm_fatal(`gfn, $sformatf("Unknown manifest line in cosim loader: %0s", line))
      end
    end

    $fclose(fd);
  endfunction

endclass
