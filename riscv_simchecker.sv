// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
// Design Name:    RISC-V Tracer                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Compares the executed instructions with a golden model     //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "riscv_config.sv"

import riscv_defines::*;

// do not import anything if the simchecker is not used
// this gets rid of warnings during simulation
`ifdef SIMCHECKER
import "DPI-C" function chandle riscv_checker_init(input int boot_addr, input int core_id, input int cluster_id);
import "DPI-C" function int     riscv_checker_step(input chandle cpu, input longint simtime, input int cycle, input logic [31:0] pc, input logic [31:0] instr);
import "DPI-C" function void    riscv_checker_irq(input chandle cpu, input int irq, input int irq_no);
import "DPI-C" function void    riscv_checker_mem_access(input chandle cpu, input int we, input logic [31:0] addr, input logic [31:0] data);
import "DPI-C" function void    riscv_checker_reg_access(input chandle cpu, input logic [31:0] addr, input logic [31:0] data);
`endif

module riscv_simchecker
(
  // Clock and Reset
  input  logic        clk,
  input  logic        rst_n,

  input  logic        fetch_enable,
  input  logic [31:0] boot_addr,
  input  logic [3:0]  core_id,
  input  logic [5:0]  cluster_id,

  input  logic [15:0] instr_compressed,
  input  logic        if_valid,
  input  logic        pc_set,

  input  logic [31:0] pc,
  input  logic [31:0] instr,
  input  logic        is_compressed,
  input  logic        id_valid,
  input  logic        is_decoding,
  input  logic        is_illegal,
  input  logic        is_interrupt,
  input  logic [4:0]  irq_no,
  input  logic        pipe_flush,

  input  logic        ex_valid,
  input  logic [ 4:0] ex_reg_addr,
  input  logic        ex_reg_we,
  input  logic [31:0] ex_reg_wdata,

  input  logic        ex_data_req,
  input  logic        ex_data_gnt,
  input  logic        ex_data_we,
  input  logic [31:0] ex_data_addr,
  input  logic [31:0] ex_data_wdata,

  input  logic        lsu_misaligned,
  input  logic        wb_bypass,

  input  logic        wb_valid,
  input  logic [ 4:0] wb_reg_addr,
  input  logic        wb_reg_we,
  input  logic [31:0] wb_reg_wdata,

  input  logic        wb_data_rvalid,
  input  logic [31:0] wb_data_rdata
);

`ifdef SIMCHECKER
  // DPI stuff
  chandle dpi_simdata;

  // SV-only stuff
  typedef struct {
    logic [ 4:0] addr;
    logic [31:0] value;
  } reg_t;

  typedef struct {
    logic [31:0] addr;
    logic        we;
    logic [ 3:0] be;
    logic [31:0] wdata;
    logic [31:0] rdata;
  } mem_acc_t;

  class instr_trace_t;
    time         simtime;
    int          cycles;
    logic [31:0] pc;
    logic [31:0] instr;
    logic        irq;
    logic [ 4:0] irq_no;
    logic        wb_bypass;
    reg_t        regs_write[$];
    mem_acc_t    mem_access[$];

    function new ();
      irq        = 1'b0;
      wb_bypass  = 1'b1;
      regs_write = {};
      mem_access = {};
    endfunction
  endclass

  mailbox rdata_stack = new (4);
  integer rdata_writes = 0;

  integer      cycles;

  logic [15:0] instr_compressed_id;
  logic        is_irq_if, is_irq_id;
  logic [ 4:0] irq_no_id, irq_no_if;

  mailbox instr_ex = new (4);
  mailbox instr_wb = new (4);

  // simchecker initialization
  initial
  begin
    wait(rst_n == 1'b1);
    wait(fetch_enable == 1'b1);

    dpi_simdata = riscv_checker_init(boot_addr, core_id, cluster_id);
  end

  // virtual ID/EX pipeline
  initial
  begin
    instr_trace_t trace;
    mem_acc_t     mem_acc;
    reg_t         reg_write;

    while(1) begin
      instr_ex.get(trace);

      // wait until we are going to the next stage
      do begin
        @(negedge clk);

        reg_write.addr  = ex_reg_addr;
        reg_write.value = ex_reg_wdata;

        if (ex_reg_we)
          trace.regs_write.push_back(reg_write);

        // look for data accesses and log them
        if (ex_data_req && ex_data_gnt) begin
          mem_acc.addr = ex_data_addr;
          mem_acc.we   = ex_data_we;

          if (mem_acc.we)
            mem_acc.wdata = ex_data_wdata;
          else
            mem_acc.wdata = 'x;

          trace.mem_access.push_back(mem_acc);
        end
      end while ((!ex_valid || lsu_misaligned) && (!wb_bypass));

      trace.wb_bypass = wb_bypass;

      instr_wb.put(trace);
    end
  end

  // virtual EX/WB pipeline
  initial
  begin
    instr_trace_t trace;
    reg_t         reg_write;
    logic [31:0]  tmp_discard;

    while(1) begin
      instr_wb.get(trace);

      if (!trace.wb_bypass) begin
        // wait until we are going to the next stage
        do begin
          @(negedge clk);
          #1;

          // pop rdata from stack when there were pending writes
          while(rdata_stack.num() > 0 && rdata_writes > 0) begin
            rdata_writes--;
            rdata_stack.get(tmp_discard);
          end

        end while (!wb_valid);

        reg_write.addr  = wb_reg_addr;
        reg_write.value = wb_reg_wdata;

        if (wb_reg_we)
          trace.regs_write.push_back(reg_write);

        // take care of rdata
        foreach(trace.mem_access[i]) begin
          if (trace.mem_access[i].we) begin
            // for writes we don't need to wait for the rdata, so if it has
            // not appeared yet, we count it and remove it later from out
            // stack
            if (rdata_stack.num() > 0)
              rdata_stack.get(tmp_discard);
            else
              rdata_writes++;

          end else begin
            if (rdata_stack.num() == 0)
              $warning("rdata stack is empty, but we are waiting for a read");

            if (rdata_writes > 0)
              $warning("rdata_writes is > 0, but we are waiting for a read");

            rdata_stack.get(trace.mem_access[i].rdata);
          end
        end
      end

      // instruction is ready now, all data is inserted
      foreach(trace.mem_access[i]) begin
        if (trace.mem_access[i].we)
          riscv_checker_mem_access(dpi_simdata, trace.mem_access[i].we, trace.mem_access[i].addr, trace.mem_access[i].wdata);
        else
          riscv_checker_mem_access(dpi_simdata, trace.mem_access[i].we, trace.mem_access[i].addr, trace.mem_access[i].rdata);
      end

      foreach(trace.regs_write[i]) begin
        riscv_checker_reg_access(dpi_simdata, trace.regs_write[i].addr, trace.regs_write[i].value);
      end

      riscv_checker_irq(dpi_simdata, trace.irq, trace.irq_no);

      if (riscv_checker_step(dpi_simdata, trace.simtime, trace.cycles, trace.pc, trace.instr))
        $display("%t: Cluster %d, Core %d: Mismatch between simulator and RTL detected", trace.simtime, cluster_id, core_id);
    end
  end

  // cycle counter
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
      cycles = 0;
    else
      cycles = cycles + 1;
  end

  // create rdata stack
  initial
  begin
    while(1) begin
      @(negedge clk);

      if (wb_data_rvalid) begin
        rdata_stack.put(wb_data_rdata);
      end
    end
  end

  always_ff @(posedge clk)
  begin
    if (pc_set) begin
      is_irq_if <= is_interrupt;
      irq_no_if <= irq_no;
    end else if (if_valid) begin
      is_irq_if <= 1'b0;
    end
  end

  always_ff @(posedge clk)
  begin
    if (if_valid) begin
      instr_compressed_id <= instr_compressed;
      is_irq_id           <= is_irq_if;
      irq_no_id           <= irq_no_if;
    end
  end

  // log execution
  initial
  begin
    instr_trace_t trace;

    while(1) begin
      @(negedge clk);

      // - special case for WFI because we don't wait for unstalling there
      // - special case for illegal instructions, since they will not go through
      //   the pipe
      if ((id_valid && is_decoding) || pipe_flush || (is_decoding && is_illegal))
      begin
        trace = new ();

        trace.simtime    = $time;
        trace.cycles      = cycles;
        trace.pc         = pc;

        if (is_compressed)
          trace.instr = {instr_compressed_id, instr_compressed_id};
        else
          trace.instr = instr;

        if (is_irq_id) begin
          trace.irq    = 1'b1;
          trace.irq_no = irq_no_id;
        end

        instr_ex.put(trace);
      end
    end
  end
`endif

endmodule
