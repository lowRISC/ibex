/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
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

// Base class for all load/store instruction stream

class riscv_load_store_base_instr_stream extends riscv_mem_access_stream;

  typedef enum bit [1:0] {
    NARROW,
    HIGH,
    MEDIUM,
    SPARSE
  } locality_e;

  rand int unsigned  num_load_store;
  rand int unsigned  num_mixed_instr;
  rand int           base;
  int                offset[];
  int                addr[];
  riscv_instr        load_store_instr[$];
  rand int unsigned  data_page_id;
  rand riscv_reg_t   rs1_reg;
  rand locality_e    locality;
  rand int           max_load_store_offset;
  rand bit           use_sp_as_rs1;

  `uvm_object_utils(riscv_load_store_base_instr_stream)

  constraint sp_rnd_order_c {
    solve use_sp_as_rs1 before rs1_reg;
  }

  constraint sp_c {
    use_sp_as_rs1 dist {1 := 1, 0 := 2};
    if (use_sp_as_rs1) {
      rs1_reg == SP;
    }
  }

  constraint rs1_c {
    !(rs1_reg inside {cfg.reserved_regs, reserved_rd, ZERO});
  }

  constraint addr_c {
    solve data_page_id before max_load_store_offset;
    solve max_load_store_offset before base;
    data_page_id < max_data_page_id;
    foreach (data_page[i]) {
      if (i == data_page_id) {
        max_load_store_offset == data_page[i].size_in_bytes;
      }
    }
    base inside {[0 : max_load_store_offset-1]};
  }

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function void randomize_offset();
    int offset_, addr_;
    offset = new[num_load_store];
    addr = new[num_load_store];
    for (int i=0; i<num_load_store; i++) begin
      if (!std::randomize(offset_, addr_) with {
        if (locality == NARROW) {
          soft offset_ inside {[-16:16]};
        } else if (locality == HIGH) {
          soft offset_ inside {[-64:64]};
        } else if (locality == MEDIUM) {
          soft offset_ inside {[-256:256]};
        } else if (locality == SPARSE) {
          soft offset_ inside {[-2048:2047]};
        }
        addr_ == base + offset_;
        addr_ inside {[0 : max_load_store_offset - 1]};
      }) begin
        `uvm_fatal(`gfn, "Cannot randomize load/store offset")
      end
      offset[i] = offset_;
      addr[i] = addr_;
    end
  endfunction

  function void pre_randomize();
    super.pre_randomize();
    if (SP inside {cfg.reserved_regs, reserved_rd}) begin
      use_sp_as_rs1 = 0;
      use_sp_as_rs1.rand_mode(0);
      sp_rnd_order_c.constraint_mode(0);
    end
  endfunction

  function void post_randomize();
    randomize_offset();
    // rs1 cannot be modified by other instructions
    if(!(rs1_reg inside {reserved_rd})) begin
      reserved_rd = {reserved_rd, rs1_reg};
    end
    gen_load_store_instr();
    add_mixed_instr(num_mixed_instr);
    add_rs1_init_la_instr(rs1_reg, data_page_id, base);
    super.post_randomize();
  endfunction

  // Generate each load/store instruction
  virtual function void gen_load_store_instr();
    bit enable_compressed_load_store, enable_zcb;
    riscv_instr instr;
    randomize_avail_regs();
    if ((rs1_reg inside {[S0 : A5], SP}) && !cfg.disable_compressed_instr) begin
      enable_compressed_load_store = 1;
    end
    if ((RV32C inside {riscv_instr_pkg::supported_isa}) &&
        (RV32ZCB inside {riscv_instr_pkg::supported_isa} && cfg.enable_zcb_extension)) begin
      enable_zcb = 1;
    end
    foreach (addr[i]) begin
      // Assign the allowed load/store instructions based on address alignment
      // This is done separately rather than a constraint to improve the randomization performance
      allowed_instr = {LB, LBU, SB};
      if((offset[i] inside {[0:2]}) && enable_compressed_load_store &&
        enable_zcb && rs1_reg != SP) begin
        `uvm_info(`gfn, "Add ZCB byte load/store to allowed instr", UVM_LOW)
        allowed_instr = {C_LBU, C_SB};
      end
      if (!cfg.enable_unaligned_load_store) begin
        if (addr[i][0] == 1'b0) begin
          allowed_instr = {LH, LHU, SH, allowed_instr};
          if(((offset[i] == 0) || (offset[i] == 2)) && enable_compressed_load_store &&
            enable_zcb && rs1_reg != SP) begin
            `uvm_info(`gfn, "Add ZCB half-word load/store to allowed instr", UVM_LOW)
            allowed_instr = {C_LHU, C_LH, C_SH};
          end
        end
        if (addr[i] % 4 == 0) begin
          allowed_instr = {LW, SW, allowed_instr};
          if (cfg.enable_floating_point) begin
            allowed_instr = {FLW, FSW, allowed_instr};
          end
          if((offset[i] inside {[0:127]}) && (offset[i] % 4 == 0) &&
             (RV32C inside {riscv_instr_pkg::supported_isa}) &&
             enable_compressed_load_store) begin
            if (rs1_reg == SP) begin
              `uvm_info(`gfn, "Add LWSP/SWSP to allowed instr", UVM_LOW)
              allowed_instr = {C_LWSP, C_SWSP};
            end else begin
              allowed_instr = {C_LW, C_SW, allowed_instr};
              if (cfg.enable_floating_point && (RV32FC inside {supported_isa})) begin
                allowed_instr = {C_FLW, C_FSW, allowed_instr};
              end
            end
          end
        end
        if ((XLEN >= 64) && (addr[i] % 8 == 0)) begin
          allowed_instr = {LWU, LD, SD, allowed_instr};
          if (cfg.enable_floating_point && (RV32D inside {supported_isa})) begin
            allowed_instr = {FLD, FSD, allowed_instr};
          end
          if((offset[i] inside {[0:255]}) && (offset[i] % 8 == 0) &&
             (RV64C inside {riscv_instr_pkg::supported_isa} &&
             enable_compressed_load_store)) begin
            if (rs1_reg == SP) begin
              allowed_instr = {C_LDSP, C_SDSP};
            end else begin
              allowed_instr = {C_LD, C_SD, allowed_instr};
              if (cfg.enable_floating_point && (RV32DC inside {supported_isa})) begin
                allowed_instr = {C_FLD, C_FSD, allowed_instr};
              end
            end
          end
        end
      end else begin // unaligned load/store
        allowed_instr = {LW, SW, LH, LHU, SH, allowed_instr};
        // Compressed load/store still needs to be aligned
        if ((offset[i] inside {[0:127]}) && (offset[i] % 4 == 0) &&
            (RV32C inside {riscv_instr_pkg::supported_isa}) &&
            enable_compressed_load_store) begin
            if (rs1_reg == SP) begin
              allowed_instr = {C_LWSP, C_SWSP};
            end else begin
              allowed_instr = {C_LW, C_SW, allowed_instr};
            end
        end
        if (XLEN >= 64) begin
          allowed_instr = {LWU, LD, SD, allowed_instr};
          if ((offset[i] inside {[0:255]}) && (offset[i] % 8 == 0) &&
              (RV64C inside {riscv_instr_pkg::supported_isa}) &&
              enable_compressed_load_store) begin
              if (rs1_reg == SP) begin
                allowed_instr = {C_LWSP, C_SWSP};
              end else begin
                allowed_instr = {C_LD, C_SD, allowed_instr};
              end
           end
        end
      end
      instr = riscv_instr::get_load_store_instr(allowed_instr);
      instr.has_rs1 = 0;
      instr.has_imm = 0;
      randomize_gpr(instr);
      instr.rs1 = rs1_reg;
      instr.imm_str = $sformatf("%0d", $signed(offset[i]));
      instr.process_load_store = 0;
      instr_list.push_back(instr);
      load_store_instr.push_back(instr);
    end
  endfunction

endclass

// A single load/store instruction
class riscv_single_load_store_instr_stream extends riscv_load_store_base_instr_stream;

  constraint legal_c {
    num_load_store == 1;
    num_mixed_instr < 5;
  }

  `uvm_object_utils(riscv_single_load_store_instr_stream)
  `uvm_object_new

endclass

// Back to back load/store instructions
class riscv_load_store_stress_instr_stream extends riscv_load_store_base_instr_stream;

  int unsigned max_instr_cnt = 30;
  int unsigned min_instr_cnt = 10;

  constraint legal_c {
    num_load_store inside {[min_instr_cnt:max_instr_cnt]};
    num_mixed_instr == 0;
  }

  `uvm_object_utils(riscv_load_store_stress_instr_stream)
  `uvm_object_new

endclass


// Back to back load/store instructions
class riscv_load_store_shared_mem_stream extends riscv_load_store_stress_instr_stream;

  `uvm_object_utils(riscv_load_store_shared_mem_stream)
  `uvm_object_new

  function void pre_randomize();
    load_store_shared_memory = 1;
    super.pre_randomize();
  endfunction

endclass

// Random load/store sequence
// A random mix of load/store instructions and other instructions
class riscv_load_store_rand_instr_stream extends riscv_load_store_base_instr_stream;

  constraint legal_c {
    num_load_store inside {[10:30]};
    num_mixed_instr inside {[10:30]};
  }

  `uvm_object_utils(riscv_load_store_rand_instr_stream)
  `uvm_object_new

endclass

// Use a small set of GPR to create various WAW, RAW, WAR hazard scenario
class riscv_hazard_instr_stream extends riscv_load_store_base_instr_stream;

  int unsigned num_of_avail_regs = 6;

  constraint legal_c {
    num_load_store inside {[10:30]};
    num_mixed_instr inside {[10:30]};
  }

  `uvm_object_utils(riscv_hazard_instr_stream)
  `uvm_object_new

  function void pre_randomize();
    avail_regs = new[num_of_avail_regs];
    super.pre_randomize();
  endfunction

endclass

// Use a small set of address to create various load/store hazard sequence
// This instruction stream focus more on hazard handling of load store unit.
class riscv_load_store_hazard_instr_stream extends riscv_load_store_base_instr_stream;

  rand int hazard_ratio;

  constraint hazard_ratio_c {
    hazard_ratio inside {[20:100]};
  }

  constraint legal_c {
    num_load_store inside {[10:20]};
    num_mixed_instr inside {[1:7]};
  }

  `uvm_object_utils(riscv_load_store_hazard_instr_stream)
  `uvm_object_new

  virtual function void randomize_offset();
    int offset_, addr_;
    offset = new[num_load_store];
    addr = new[num_load_store];
    for (int i = 0; i < num_load_store; i++) begin
      if ((i > 0) && ($urandom_range(0, 100) < hazard_ratio)) begin
        offset[i] = offset[i-1];
        addr[i] = addr[i-1];
      end else begin
        if (!std::randomize(offset_, addr_) with {
          if (locality == NARROW) {
            soft offset_ inside {[-16:16]};
          } else if (locality == HIGH) {
            soft offset_ inside {[-64:64]};
          } else if (locality == MEDIUM) {
            soft offset_ inside {[-256:256]};
          } else if (locality == SPARSE) {
            soft offset_ inside {[-2048:2047]};
          }
          addr_ == base + offset_;
          addr_ inside {[0 : max_load_store_offset - 1]};
        }) begin
          `uvm_fatal(`gfn, "Cannot randomize load/store offset")
        end
        offset[i] = offset_;
        addr[i] = addr_;
      end
    end
  endfunction : randomize_offset

endclass

// Back to back access to multiple data pages
// This is useful to test data TLB switch and replacement
class riscv_multi_page_load_store_instr_stream extends riscv_mem_access_stream;

  riscv_load_store_stress_instr_stream load_store_instr_stream[];
  rand int unsigned num_of_instr_stream;
  rand int unsigned data_page_id[];
  rand riscv_reg_t  rs1_reg[];

  constraint default_c {
    foreach(data_page_id[i]) {
      data_page_id[i] < max_data_page_id;
    }
    data_page_id.size() == num_of_instr_stream;
    rs1_reg.size() == num_of_instr_stream;
    unique {rs1_reg};
    foreach(rs1_reg[i]) {
      !(rs1_reg[i] inside {cfg.reserved_regs, ZERO});
    }
  }

  constraint page_c {
    solve num_of_instr_stream before data_page_id;
    num_of_instr_stream inside {[1 : max_data_page_id]};
    unique {data_page_id};
  }

  // Avoid accessing a large number of pages because we may run out of registers for rs1
  // Each page access needs a reserved register as the base address of load/store instruction
  constraint reasonable_c {
    num_of_instr_stream inside {[2:8]};
  }

  `uvm_object_utils(riscv_multi_page_load_store_instr_stream)
  `uvm_object_new

  // Generate each load/store seq, and mix them together
  function void post_randomize();
    load_store_instr_stream = new[num_of_instr_stream];
    foreach(load_store_instr_stream[i]) begin
      load_store_instr_stream[i] = riscv_load_store_stress_instr_stream::type_id::
                                   create($sformatf("load_store_instr_stream_%0d", i));
      load_store_instr_stream[i].min_instr_cnt = 5;
      load_store_instr_stream[i].max_instr_cnt = 10;
      load_store_instr_stream[i].cfg = cfg;
      load_store_instr_stream[i].hart = hart;
      load_store_instr_stream[i].sp_c.constraint_mode(0);
      // Make sure each load/store sequence doesn't override the rs1 of other sequences.
      foreach(rs1_reg[j]) begin
        if(i != j) begin
          load_store_instr_stream[i].reserved_rd =
            {load_store_instr_stream[i].reserved_rd, rs1_reg[j]};
        end
      end
      `DV_CHECK_RANDOMIZE_WITH_FATAL(load_store_instr_stream[i],
                                     rs1_reg == local::rs1_reg[i];
                                     data_page_id == local::data_page_id[i];,
                                     "Cannot randomize load/store instruction")
      // Mix the instruction stream of different page access, this could trigger the scenario of
      // frequent data TLB switch
      if(i == 0) begin
        instr_list = load_store_instr_stream[i].instr_list;
      end else begin
        mix_instr_stream(load_store_instr_stream[i].instr_list);
      end
    end
  endfunction

endclass

// Access the different locations of the same memory regions
class riscv_mem_region_stress_test extends riscv_multi_page_load_store_instr_stream;

  `uvm_object_utils(riscv_mem_region_stress_test)
  `uvm_object_new

  constraint page_c {
    num_of_instr_stream inside {[2:5]};
    foreach (data_page_id[i]) {
      if (i > 0) {
        data_page_id[i] == data_page_id[i-1];
      }
    }
  }

endclass

// Random load/store sequence to full address range
// The address range is not preloaded with data pages, use store instruction to initialize first
class riscv_load_store_rand_addr_instr_stream extends riscv_load_store_base_instr_stream;

  rand bit [XLEN-1:0] addr_offset;

  // Find an unused 4K page from address 1M onward
  constraint addr_offset_c {
    |addr_offset[XLEN-1:20] == 1'b1;
    // TODO(taliu) Support larger address range
    addr_offset[XLEN-1:31] == 0;
    addr_offset[11:0] == 0;
  }

  constraint legal_c {
    num_load_store inside {[5:10]};
    num_mixed_instr inside {[5:10]};
  }

  `uvm_object_utils(riscv_load_store_rand_addr_instr_stream)
  `uvm_object_new

   virtual function void randomize_offset();
    int offset_, addr_;
    offset = new[num_load_store];
    addr = new[num_load_store];
    for (int i=0; i<num_load_store; i++) begin
      if (!std::randomize(offset_) with {
          offset_ inside {[-2048:2047]};
        }
      ) begin
        `uvm_fatal(`gfn, "Cannot randomize load/store offset")
      end
      offset[i] = offset_;
      addr[i] = addr_offset + offset_;
    end
  endfunction

  virtual function void add_rs1_init_la_instr(riscv_reg_t gpr, int id, int base = 0);
    riscv_instr instr[$];
    riscv_pseudo_instr li_instr;
    riscv_instr store_instr;
    riscv_instr add_instr;
    int min_offset[$];
    int max_offset[$];
    min_offset = offset.min();
    max_offset = offset.max();
    // Use LI to initialize the address offset
    li_instr = riscv_pseudo_instr::type_id::create("li_instr");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(li_instr,
       pseudo_instr_name == LI;
       rd inside {cfg.gpr};
       rd != gpr;
    )
    li_instr.imm_str = $sformatf("0x%0x", addr_offset);
    // Add offset to the base address
    add_instr = riscv_instr::get_instr(ADD);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(add_instr,
       rs1 == gpr;
       rs2 == li_instr.rd;
       rd  == gpr;
    )
    instr.push_back(li_instr);
    instr.push_back(add_instr);
    // Create SW instruction template
    store_instr = riscv_instr::get_instr(SB);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(store_instr,
       instr_name == SB;
       rs1 == gpr;
    )
    // Initialize the location which used by load instruction later
    foreach (load_store_instr[i]) begin
      if (load_store_instr[i].category == LOAD) begin
        riscv_instr store;
        store = riscv_instr::type_id::create("store");
        store.copy(store_instr);
        store.rs2 = riscv_reg_t'(i % 32);
        store.imm_str = load_store_instr[i].imm_str;
        // TODO: C_FLDSP is in both rv32 and rv64 ISA
        case (load_store_instr[i].instr_name) inside
          LB, LBU : store.instr_name = SB;
          LH, LHU : store.instr_name = SH;
          LW, C_LW, C_LWSP, FLW, C_FLW, C_FLWSP : store.instr_name = SW;
          LD, C_LD, C_LDSP, FLD, C_FLD, LWU     : store.instr_name = SD;
          default : `uvm_fatal(`gfn, $sformatf("Unexpected op: %0s",
                                               load_store_instr[i].convert2asm()))
        endcase
        instr.push_back(store);
      end
    end
    instr_list = {instr, instr_list};
    super.add_rs1_init_la_instr(gpr, id, 0);
  endfunction

endclass

class riscv_vector_load_store_instr_stream extends riscv_mem_access_stream;

  typedef enum {UNIT_STRIDED, STRIDED, INDEXED} address_mode_e;

  rand bit [10:0] eew;
  rand int unsigned data_page_id;
  rand int unsigned num_mixed_instr;
  rand int unsigned stride_byte_offset;
  rand int unsigned index_addr;
  rand address_mode_e address_mode;
  rand riscv_reg_t rs1_reg;  // Base address
  rand riscv_reg_t rs2_reg;  // Stride offset
  riscv_vreg_t vs2_reg;      // Index address

  constraint vec_mixed_instr_c {
    num_mixed_instr inside {[0:10]};
  }

  constraint eew_c {
    eew inside {cfg.vector_cfg.legal_eew};
  }

  constraint stride_byte_offset_c {
    solve eew before stride_byte_offset;
    // Keep a reasonable byte offset range to avoid vector memory address overflow
    stride_byte_offset inside {[1 : 128]};
    stride_byte_offset % (eew / 8) == 1;
  }

  constraint index_addr_c {
    solve eew before index_addr;
    // Keep a reasonable index address range to avoid vector memory address overflow
    index_addr inside {[0 : 128]};
    index_addr % (eew / 8) == 1;
  }

  constraint vec_rs_c {
    !(rs1_reg inside {cfg.reserved_regs, reserved_rd, ZERO});
    !(rs2_reg inside {cfg.reserved_regs, reserved_rd, ZERO});
    rs1_reg != rs2_reg;
  }

  constraint vec_data_page_id_c {
    data_page_id < max_data_page_id;
  }

  int base;
  int max_load_store_addr;
  riscv_vector_instr load_store_instr;

  `uvm_object_utils(riscv_vector_load_store_instr_stream)
  `uvm_object_new

  function void post_randomize();
    reserved_rd = {reserved_rd, rs1_reg, rs2_reg};
    randomize_avail_regs();
    gen_load_store_instr();
    randomize_addr();
    add_mixed_instr(num_mixed_instr);
    add_rs1_init_la_instr(rs1_reg, data_page_id, base);
    if (address_mode == STRIDED) begin
      instr_list.push_front(get_init_gpr_instr(rs2_reg, stride_byte_offset));
    end else if (address_mode == INDEXED) begin
      // TODO: Support different index address for each element
      add_init_vector_gpr_instr(vs2_reg, index_addr);
    end
    super.post_randomize();
  endfunction

  virtual function void randomize_addr();
    int ss = address_span();
    bit success;

    repeat (10) begin
      max_load_store_addr = data_page[data_page_id].size_in_bytes - ss;
      if (max_load_store_addr >= 0) begin
        success = 1'b1;
        break;
      end
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_page_id, data_page_id < max_data_page_id;)
    end

    assert (success) else begin
      `uvm_fatal(`gfn, $sformatf({"Expected positive value for max_load_store_addr, got %0d.",
        "  Perhaps more memory needs to be allocated in the data pages for vector loads and stores.",
        "\ndata_page_id:%0d\ndata_page[data_page_id].size_in_bytes:%0d\naddress_span:%0d",
        "\nstride_bytes:%0d\nVLEN:%0d\nLMUL:%0d\ncfg.vector_cfg.vtype.vsew:%0d\n\n"},
        max_load_store_addr, data_page_id, data_page[data_page_id].size_in_bytes, ss,
        stride_bytes(), VLEN, cfg.vector_cfg.vtype.vlmul, cfg.vector_cfg.vtype.vsew))
    end

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(base, base inside {[0 : max_load_store_addr]};
                                             base % eew == 0;)
  endfunction

  virtual function int address_span();
    int num_elements = VLEN * cfg.vector_cfg.vtype.vlmul / cfg.vector_cfg.vtype.vsew;
    case (address_mode)
      UNIT_STRIDED : address_span = num_elements * stride_bytes();
      STRIDED      : address_span = num_elements * stride_byte_offset;
      INDEXED      : address_span = index_addr + num_elements * stride_bytes();
    endcase
  endfunction

  virtual function int stride_bytes();
    stride_bytes = eew / 8;
  endfunction

  // Generate each load/store instruction
  virtual function void gen_load_store_instr();
    build_allowed_instr();
    randomize_vec_load_store_instr();
    instr_list.push_back(load_store_instr);
  endfunction

  virtual function void build_allowed_instr();
    case (address_mode)
      UNIT_STRIDED : begin
        allowed_instr = {VLE_V, VSE_V, allowed_instr};
        if (cfg.vector_cfg.enable_fault_only_first_load) begin
          allowed_instr = {VLEFF_V, allowed_instr};
        end
        if (cfg.vector_cfg.enable_zvlsseg) begin
          allowed_instr = {VLSEGE_V, VSSEGE_V, allowed_instr};
          if (cfg.vector_cfg.enable_fault_only_first_load) begin
            allowed_instr = {VLSEGEFF_V, allowed_instr};
          end
        end
      end
      STRIDED : begin
        allowed_instr = {VLSE_V, VSSE_V, allowed_instr};
        if (cfg.vector_cfg.enable_zvlsseg) begin
          allowed_instr = {VLSSEGE_V, VSSSEGE_V, allowed_instr};
        end
      end
      INDEXED : begin
        allowed_instr = {VLXEI_V, VSXEI_V, VSUXEI_V, allowed_instr};
        if (cfg.vector_cfg.enable_zvlsseg) begin
          allowed_instr = {VLXSEGEI_V, VSXSEGEI_V, VSUXSEGEI_V, allowed_instr};
        end
      end
    endcase
  endfunction

  virtual function void randomize_vec_load_store_instr();
    $cast(load_store_instr, riscv_instr::get_load_store_instr(allowed_instr));
    load_store_instr.m_cfg = cfg;
    load_store_instr.has_rs1 = 0;
    load_store_instr.has_vs2 = 1;
    load_store_instr.has_imm = 0;
    randomize_gpr(load_store_instr);
    load_store_instr.rs1 = rs1_reg;
    load_store_instr.rs2 = rs2_reg;
    load_store_instr.vs2 = vs2_reg;
    if (address_mode == INDEXED) begin
      cfg.vector_cfg.reserved_vregs = {load_store_instr.vs2};
      vs2_reg = load_store_instr.vs2;
      `uvm_info(`gfn, $sformatf("vs2_reg = v%0d", vs2_reg), UVM_LOW)
    end
    load_store_instr.process_load_store = 0;
  endfunction

endclass

// Class to test Zcmp Push/Popret control flow chains
class riscv_zcmp_chain_instr_stream extends riscv_mem_access_stream;
  // Number of push/pop blocks in the chain
  rand int unsigned   num_blocks;
  // Execution order of these blocks
  int unsigned        block_order[];

  // Track number of chains
  static int unsigned chain_cnt = 0;
  int unsigned        chain_id;

  // Data page to use for stack operations
  rand int            base;
  rand int unsigned   data_page_id;
  rand int unsigned   max_load_store_offset;

  constraint addr_c {
    solve data_page_id before max_load_store_offset;
    solve max_load_store_offset before base;
    data_page_id < max_data_page_id;
    foreach (data_page[i]) {
      if (i == data_page_id) {max_load_store_offset == data_page[i].size_in_bytes;}
    }
    base inside {[0 : max_load_store_offset - 1]};
  }

  constraint block_c {num_blocks inside {[1 : 50]};}

  function new(string name = "");
    super.new(name);
    // Assign a unique ID to this specific stream instance
    chain_id = chain_cnt++;
  endfunction

  `uvm_object_utils(riscv_zcmp_chain_instr_stream)

  function void post_randomize();
    // SP cannot be modified by other instructions
    if (!(SP inside {reserved_rd})) begin
      reserved_rd = {reserved_rd, SP};
    end
    setup_chain_order();

    // Generate the chain of blocks
    gen_zcmp_chain();
    // Ensure labels are preserved
    foreach (instr_list[i]) begin
      if (instr_list[i].label != "") instr_list[i].has_label = 1'b1;
      else instr_list[i].has_label = 1'b0;
      instr_list[i].atomic = 1'b1;
    end
    // Initizialize SP to point to a data page
    add_rs1_init_la_instr(SP, data_page_id, 0);
    // Don't call super here, because it will delete all labels
  endfunction

  // Randomize the order in which blocks are executed
  virtual function void setup_chain_order();
    block_order = new[num_blocks];
    foreach (block_order[i]) begin
      block_order[i] = i;
    end
    block_order.shuffle();
  endfunction

  // Main generator function
  virtual function void gen_zcmp_chain();
    riscv_instr instr;
    riscv_instr popret_instr;
    string prefix = $sformatf("zcmp_%0d", chain_id);
    riscv_instr_name_t exclude_instr[];
    update_excluded_instr(exclude_instr);

    // Save all registers that will be overwritten by our upcoming push/pop chain
    // A0 is overwritten by CM.POPRETZ, but cannot be saved by CM.PUSH/POP.
    // Save A0 outside the main stack frame (e.g., at SP-120)
    instr = riscv_instr::get_instr(ADDI);
    instr.rd = SP;
    instr.rs1 = SP;
    instr.imm_str = "-16";
    instr_list.push_back(instr);
    instr = riscv_instr::get_instr(XLEN == 32 ? SW : SD);
    instr.rs1 = SP;
    instr.rs2 = A0;
    instr.imm_str = "0";
    instr_list.push_back(instr);
    // Save all the remaining registers overwritten by pop
    instr = riscv_instr::get_instr(CM_PUSH);
    instr.stack_adj = -112; // Max stack frame
    instr.rlist = 15; // All registers
    instr_list.push_back(instr);
    // Jump to the first block
    instr = riscv_instr::get_instr(JAL);
    instr.rd = ZERO; // Don't link, just jump
    instr.imm_str = $sformatf("%s_%0d", prefix, block_order[0]);
    instr.comment = "Bootstrap: Jump to first random block";
    instr_list.push_back(instr);

    // Generate the push/pop blocks
    for (int i = 0; i < num_blocks; i++) begin
      // Number of random instructions to insert between push/pop
      int random_instructions;
      // Labels to link blocks
      string current_label = $sformatf("%s_%0d", prefix, i);
      string next_label;
      int next_block_idx = -1;
      // Control the stack growth/shrinkage
      // Total number of instructions (Push + Pop)
      int num_steps;
      // Stack size at each step
      int stack_size[];
      int max_stack = max_load_store_offset;
      int delta;
      riscv_instr_name_t final_opcode;

      // Find which block comes after current block 'i' in the execution order
      foreach (block_order[k]) begin
        if (block_order[k] == i) begin
          if (k < num_blocks - 1) begin
            next_block_idx = block_order[k+1];
            next_label = $sformatf("%s_%0d", prefix, next_block_idx);
          end else begin
            // End of chain
            next_label = $sformatf("%s_end", prefix);
          end
        end
      end

      // Randomize the stack pointer's path and the number of steps
      std::randomize(stack_size, num_steps) with {
        // Number of push/pop steps per block
        num_steps inside {[2:12]};
        // Include the initial zero depth
        stack_size.size() == num_steps + 1;
        // Start and stop at zero depth
        stack_size[0] == 0;
        stack_size[num_steps] == 0;
        foreach (stack_size[i]) {
          // Stay within stack region
          stack_size[i] inside {[-max_stack:0]};
          // Transition Constraints
          if (i > 0) {
            // Must be 16-byte aligned steps
            (stack_size[i] - stack_size[i-1]) % 16 == 0;
            // Restrict adjustment size of single push/pop and avoid no-ops (diff==0)
            (stack_size[i] - stack_size[i-1]) inside {[-112:-16], [16:112]};
          }
        }
      };

      // Loop through all the steps and insert a push or pop instruction. Also sprinkle in some
      // random instructions inbetween. Skip the very last pop, since that will be a popret we
      // handle specially.
      for (int i = 0; i < num_steps - 1; i++) begin
        delta = stack_size[i+1] - stack_size[i];
        if (delta < 0) begin
          // CM.PUSH (Stack Grows)
          instr = riscv_instr::get_instr(CM_PUSH);
          `DV_CHECK_RANDOMIZE_WITH_FATAL(instr, stack_adj == delta;)
        end else begin
          // CM.POP (Stack Shrinks)
          instr = riscv_instr::get_instr(CM_POP);
          `DV_CHECK_RANDOMIZE_WITH_FATAL(instr, stack_adj == delta;)
        end

        // First instruction gets the label to jump to
        if (i == 0) begin
          instr.label = current_label;
        end

        instr_list.push_back(instr);

        // Insert random instructions in between push and pops
        random_instructions = $urandom_range(0, 5);
        repeat (random_instructions) begin
          instr = riscv_instr::get_rand_instr(.include_category({ARITHMETIC, LOGICAL, SHIFT, COMPARE
                                                                }), .exclude_instr(exclude_instr));
          `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
            // CRITICAL: Do not touch SP!
            if (cfg.reserved_regs.size() > 0 || reserved_rd.size() > 0) {
              !(rd inside {cfg.reserved_regs, reserved_rd});
            },
            $sformatf("Cannot randomize instruction %s with constrained registers\n",
            instr.convert2asm()))
          instr_list.push_back(instr);
        end
      end

      // Last step is a POPRET/POPRETZ. Randomly choose which:
      randcase
        1: final_opcode = CM_POPRET;
        1: final_opcode = CM_POPRETZ;
      endcase
      delta = stack_size[num_steps] - stack_size[num_steps-1];
      // Do not insert this popret into the instruction stream yet. First, we have to create a
      // proper RA address to jump to. However, since we need to know where the POPRET will load the
      // RA from (i.e., which rlist and stack_adj it uses), we have to randomize it first.
      popret_instr = riscv_instr::get_instr(final_opcode);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(popret_instr, stack_adj == delta;)

      // Push the RA with the address of 'next_label' onto the stack at the correct location. The
      // following instructiosn are "atomic" because we don't want other instructions to interleave
      // between them.
      if (next_label != "") begin
        riscv_pseudo_instr la_instr_pseudo;
        riscv_reg_t temp_reg;
        int ra_offset_in_stack;

        // Calculate where RA will be read from by the POPRET instruction.
        // For cm.pop {ra, s0-sN}, stack_adj:
        // RA is usually at `[SP + stack_adj - XLEN/8*(rlist - 3)]` because we pop rlist-3 registers
        // There is one exception, if rlist == 15 (all registers), we pop rlist-2 registers because
        // it includes s10 and s11. So adjust accordingly.
        ra_offset_in_stack = delta - XLEN / 8 * (popret_instr.rlist - 3);
        if (popret_instr.rlist == 15) begin
          ra_offset_in_stack = ra_offset_in_stack - XLEN / 8;
        end

        // Get a temp reg that isn't reserved and not X0
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            temp_reg, !(temp_reg inside {cfg.reserved_regs, reserved_rd, ZERO});)

        // Load Address of the NEXT block
        la_instr_pseudo = riscv_pseudo_instr::type_id::create("la_instr_pseudo");
        la_instr_pseudo.pseudo_instr_name = LA;
        la_instr_pseudo.rd = temp_reg;
        la_instr_pseudo.imm_str = next_label;
        la_instr_pseudo.atomic = 1'b1;
        instr_list.push_back(la_instr_pseudo);

        // Overwrite the RA slot on the stack
        instr = riscv_instr::get_instr(XLEN == 32 ? SW : SD);
        instr.rs1 = SP;
        instr.rs2 = temp_reg;
        instr.imm_str = $sformatf("%0d", ra_offset_in_stack);
        instr.atomic = 1'b1;
        instr.comment = "Overwrite saved RA with next block address";
        instr_list.push_back(instr);
      end

      // Insert popret at the very end. We already randomized it earlier to place the RA at the correct address.
      instr_list.push_back(popret_instr);
    end

    // Endpoint of chain: Restore all registers overwritten by push/pop
    instr = riscv_instr::get_instr(CM_POP);
    instr.stack_adj = 112; // Max stack frame
    instr.rlist = 15; // All registers
    instr.label = $sformatf("%s_end", prefix);
    instr.comment = "End of Zcmp Chain";
    instr_list.push_back(instr);
    // Restore A0 from the stack
    instr = riscv_instr::get_instr(XLEN == 32 ? LW : LD);
    instr.rd = A0;
    instr.rs1 = SP;
    instr.imm_str = "0";
    instr_list.push_back(instr);
    instr = riscv_instr::get_instr(ADDI);
    instr.rd = SP;
    instr.rs1 = SP;
    instr.imm_str = "16";
    instr_list.push_back(instr);
  endfunction

endclass
