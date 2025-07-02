// Copyleft 2025 ISOLDE 

`include "MemStatisticsCallback.svh"

module perfCounters #(
    parameter logic [31:0] MMIO_ADDR = 32'h8000_0000
) (
    input logic clk_i,
    input logic rst_ni,
    isolde_tcdm_if.slave tcdm_slave_i,
    output logic sim_exit_o,
    MemStatisticsCallback mem_statistics_cb
);

  // Internal MMIO address mapping
  localparam logic [31:0] MMADDR_EXIT = MMIO_ADDR + 32'h0;
  localparam logic [31:0] MMADDR_PRINT = MMIO_ADDR + 32'h4;
  localparam logic [31:0] MMADDR_TTY = MMIO_ADDR + 32'h8;
  localparam logic [31:0] MMADDR_PERF = MMIO_ADDR + 32'hC;


  logic [31:0] cycle_counter;
  logic        mmio_rvalid;
  logic        mmio_req;
  logic        mmio_gnt;
  logic [31:0] mmio_rdata;
  //
  logic        perfcnt_rvalid;
  logic        perfcnt_req;
  logic        perfcnt_gnt;
  logic [31:0] perfcnt_rdata;


  int          fh_csv;  //filehandle


  // performance counters FSM states
  typedef enum logic [2:0] {
    IDLE,
    LATCH,
    WAIT,
    DIFF,
    PRINT
  } perfcnt_state_t;

  typedef struct packed {
    int cnt_wr;
    int cnt_rd;
  } mem_io_t;

  typedef struct packed {
    logic [31:0] id;
    logic [31:0] cycle_counter;
    mem_io_t imem;
    mem_io_t dmem;
    mem_io_t stack_mem;
  } perfcnt_t;

  //address decode
  always_comb begin
    mmio_req    = rst_ni && tcdm_slave_i.req.req && (tcdm_slave_i.req.addr >= MMIO_ADDR) && (tcdm_slave_i.req.addr < MMADDR_PERF) ;
    perfcnt_req = rst_ni && tcdm_slave_i.req.req && (tcdm_slave_i.req.addr >= MMADDR_PERF);
  end

  always_comb begin
    mmio_gnt = mmio_req;
    perfcnt_gnt = perfcnt_req;
  end
  //mux output
  assign tcdm_slave_i.rsp.gnt = mmio_req ? mmio_gnt : perfcnt_req ? perfcnt_gnt : '0;

  assign tcdm_slave_i.rsp.data  = mmio_rvalid ? mmio_rdata : perfcnt_rvalid ? perfcnt_rdata : 32'hDEAD_BEAF;

  assign tcdm_slave_i.rsp.valid = mmio_rvalid | perfcnt_rvalid;

  // 


  perfcnt_state_t perfcnt_state, perfcnt_next;
  perfcnt_t perfcnt_d, perfcnt_q;

  always_ff @(posedge clk_i) begin
    if (~rst_ni) begin
      perfcnt_d <= '0;
      perfcnt_q <= '0;
      perfcnt_state = IDLE;
    end else begin
      perfcnt_state <= perfcnt_next;
      case (perfcnt_next)
        LATCH: begin
          perfcnt_d.id <= tcdm_slave_i.req.data;
          perfcnt_d.cycle_counter <= cycle_counter;
          perfcnt_d.dmem.cnt_wr <= mem_statistics_cb.dataMemWrites();
          perfcnt_d.dmem.cnt_rd <= mem_statistics_cb.dataMemReads();
          perfcnt_d.imem.cnt_rd <= mem_statistics_cb.instrMemReads();
          perfcnt_d.stack_mem.cnt_wr <= mem_statistics_cb.stackMemWrites();
          perfcnt_d.stack_mem.cnt_rd <= mem_statistics_cb.stackMemReads();
          //$display("LATCH @%t id=%d,cycle_counter=%d\n",$time, tcdm_slave_i.req.data,cycle_counter);
        end
        DIFF: begin
          perfcnt_q.id <= perfcnt_d.id;
          perfcnt_q.cycle_counter <= (cycle_counter - perfcnt_d.cycle_counter);
          perfcnt_q.dmem.cnt_wr <= (mem_statistics_cb.dataMemWrites() - perfcnt_d.dmem.cnt_wr);
          perfcnt_q.dmem.cnt_rd <= (mem_statistics_cb.dataMemReads() - perfcnt_d.dmem.cnt_rd);
          //
          perfcnt_q.imem.cnt_rd <= (mem_statistics_cb.instrMemReads() - perfcnt_d.imem.cnt_rd);
          //
          perfcnt_q.stack_mem.cnt_wr <= ( mem_statistics_cb.stackMemWrites() - perfcnt_d.stack_mem.cnt_wr);
          perfcnt_q.stack_mem.cnt_rd <= ( mem_statistics_cb.stackMemReads() - perfcnt_d.stack_mem.cnt_rd);

          //$display("DIFF @%t id=%d,cycle_counter=%h\n",$time,  perfcnt_d.id, cycle_counter);
        end
        PRINT: begin
          //$display("PRINT @%t id=%d,cycles =%d\n", $time, perfcnt_q.id, perfcnt_q.cycle_counter);
          $fwrite(fh_csv, "%d,%d,", perfcnt_q.id, perfcnt_q.cycle_counter);
          $fwrite(fh_csv, "%d,", perfcnt_q.imem.cnt_rd);
          $fwrite(fh_csv, "%d,", perfcnt_q.dmem.cnt_wr);
          $fwrite(fh_csv, "%d,", perfcnt_q.dmem.cnt_rd);
          $fwrite(fh_csv, "%d,", perfcnt_q.stack_mem.cnt_wr);
          $fwrite(fh_csv, "%d,", perfcnt_q.stack_mem.cnt_rd);
          $fwrite(fh_csv, "%d,%s\n", mem_statistics_cb.instrMemLatency(), mem_statistics_cb.strInfo());
        end
      endcase
    end

  end


  always_comb begin
    if (perfcnt_req && tcdm_slave_i.req.we && (tcdm_slave_i.req.addr == MMADDR_PERF)) begin
      case (perfcnt_state)
        IDLE: begin
          perfcnt_next = LATCH;
        end
        WAIT: begin
          perfcnt_next = DIFF;
        end
      endcase
    end else begin
      case (perfcnt_state)
        LATCH: begin
          perfcnt_next = WAIT;
        end
        DIFF: begin
          perfcnt_next = PRINT;
        end
        PRINT: begin
          perfcnt_next = IDLE;
        end
      endcase
    end
  end

  /**
read performance counters implementation
**/

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) perfcnt_rvalid <= '0;
    else begin
      if (perfcnt_req) begin
        perfcnt_rvalid <= 1;
        if (~tcdm_slave_i.req.we) begin
          case (tcdm_slave_i.req.addr)
            MMADDR_PERF: perfcnt_rdata <= perfcnt_q.id;
            MMADDR_PERF + 32'h4: perfcnt_rdata <= perfcnt_q.cycle_counter;
            MMADDR_PERF + 32'h8: perfcnt_rdata <= perfcnt_q.imem.cnt_wr;
            MMADDR_PERF + 32'hC: perfcnt_rdata <= perfcnt_q.imem.cnt_rd;
            MMADDR_PERF + 32'h10: perfcnt_rdata <= perfcnt_q.dmem.cnt_wr;
            MMADDR_PERF + 32'h14: perfcnt_rdata <= perfcnt_q.dmem.cnt_rd;
            MMADDR_PERF + 32'h18: perfcnt_rdata <= perfcnt_q.stack_mem.cnt_wr;
            MMADDR_PERF + 32'h1C: perfcnt_rdata <= perfcnt_q.stack_mem.cnt_rd;
            default: perfcnt_rdata <= '0;
          endcase
        end
      end else perfcnt_rvalid = '0;
    end
  end




  always_ff @(posedge clk_i) begin
    if (~rst_ni) begin
      cycle_counter <= '0;
      mmio_rvalid <= 0;
      sim_exit_o <= 0;
    end else cycle_counter <= cycle_counter + 1;

    if (mmio_gnt) begin
      case (tcdm_slave_i.req.addr)
        MMADDR_EXIT: begin
          if (tcdm_slave_i.req.we) begin
            sim_exit_o  <= 1;
            mmio_rdata  <= tcdm_slave_i.req.data;
            mmio_rvalid <= 1;
          end else begin
            mmio_rdata  <= cycle_counter + 1;
            mmio_rvalid <= 1;
          end

        end
        MMADDR_PRINT:
        if (tcdm_slave_i.req.we) begin
          $write("%c", tcdm_slave_i.req.data);
          /**
** The semantics of the r_valid signal are not well defined with respect to the usual TCDM protocol. 
** In PULP clusters, r_valid will be asserted also after write transactions, not only in reads. 
** https://hwpe-doc.readthedocs.io/en/latest/protocols.html#hwpe-mem
** see also https://ibex-core.readthedocs.io/en/latest/03_reference/load_store_unit.html
**/
          mmio_rvalid <= 1;
        end
        MMADDR_TTY:
        if (tcdm_slave_i.req.we) begin
          $display("TTY @t=%0t: %h", $time, tcdm_slave_i.req.data);
          mmio_rvalid <= 1;
        end
        default: begin
          mmio_rdata  <= '0;
          mmio_rvalid <= 0;
        end
      endcase
    end else mmio_rvalid <= 0;

  end


  initial begin

    fh_csv = $fopen("perfcnt.csv", "w");
    if (fh_csv == 0) begin
      $display("ERROR: Could not open perfcnt.csv for writing");
      $finish;
    end else begin
      $fwrite(
          fh_csv,
          "id,cycles,reads[imemory],writes[dmemory],reads[dmemory],writes[stack],reads[stack],latency,info\n");
    end
  end

  // Close the CSV output file at the end of simulation to ensure all data is written properly.
  final begin
    if (fh_csv != 0) begin
      $fclose(fh_csv);
    end
  end
endmodule
