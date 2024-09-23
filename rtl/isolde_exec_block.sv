// Copyleft

module isolde_exec_block
  import isolde_decoder_pkg::*;
  import isolde_register_file_pkg::RegAddrWidth;
  import isolde_register_file_pkg::RegSize, isolde_register_file_pkg::RegDataWidth;
#(
    parameter string LogName = "isolde_exec_block.log"
) (
    // ISOLDE register file
           isolde_register_file_if isolde_rf_bus,
           isolde_fetch2exec_if    isolde_exec_from_decoder,
    output logic                   isolde_exec_busy_o
);


`ifndef SYNTHESIS
  integer log_fh;

  initial begin
    log_fh = $fopen(LogName, "w");
  end

  final begin
    $fclose(log_fh);
  end
`endif

  // FSM states
  typedef enum logic [1:0] {
    IDLE,
    START,  //start execution
    WAIT    //wait for completion
  } state_t;

  state_t ievli_state, ievli_next;
  logic clk;
  logic g_rst_n;
  logic start_exec;
  isolde_opcode_e isolde_opcode_dec;  //decoded isolde opcode
  logic [2:0] cnt, cnt_max;



  assign clk = isolde_exec_from_decoder.clk_i;
  assign g_rst_n = isolde_exec_from_decoder.rst_ni;
  //assign start_exec = (isolde_exec_from_decoder.isolde_decoder_enable & isolde_exec_from_decoder.isolde_decoder_ready);
  assign start_exec = isolde_exec_from_decoder.isolde_decoder_ready;
  assign isolde_exec_from_decoder.stall_isolde_decoder = isolde_exec_busy_o;
  assign isolde_opcode_dec = isolde_exec_from_decoder.isolde_opcode;

  always_ff @(posedge clk or negedge g_rst_n) begin
    if (!g_rst_n) begin
      cnt <= 0;
      ievli_state <= IDLE;
    end else begin
      ievli_state <= ievli_next;
      case (ievli_next)
        START: begin
          cnt <= 1;
          case (isolde_opcode_dec)
            isolde_opcode_nop: start_nop();
            isolde_opcode_vle32_4: start_vle32_4();
            isolde_opcode_gemm: start_gemm();
            isolde_opcode_conv2d: start_conv2d();
            default: begin
              cnt_max <= 4;  //dummy value
            end
          endcase
        end
        WAIT: begin
          cnt <= cnt + 1;
        end
      endcase
    end
  end


  always_comb begin
    case (ievli_state)
      IDLE: begin
        if (start_exec) begin
          ievli_next = START;
          isolde_exec_busy_o = 1;
        end else begin
          ievli_next = IDLE;
          isolde_exec_busy_o = 0;
        end
      end

      START: begin
        isolde_exec_busy_o = 1;
        ievli_next = WAIT;
      end

      WAIT: begin
        if (cnt == cnt_max) begin
          isolde_exec_busy_o = 0;
          ievli_next = start_exec ? START : IDLE;
        end
      end
    endcase
  end

  task static start_nop;
`ifndef SYNTHESIS
    $fwrite(log_fh, " --- %s\n", "isolde_exec_block::start_nop");
`endif
    begin
      ievli_state <= IDLE;  // resume with next cycle
    end
  endtask

  task static start_vle32_4;
`ifndef SYNTHESIS
    $fwrite(log_fh, " ---    %s\n", "isolde_exec_block::start_vle32_4");
    $fwrite(log_fh, "     rd=%d\n", isolde_exec_from_decoder.rd);
    $fwrite(log_fh, "     Q[%d] = [ %d, %d, %d, %d ]\n", isolde_exec_from_decoder.rd, isolde_rf_bus.echo_0[0], isolde_rf_bus.echo_0[1], isolde_rf_bus.echo_0[2], isolde_rf_bus.echo_0[3]);
`endif
    begin
      ievli_state <= IDLE;  // resume with next cycle
    end
  endtask

  task static start_gemm;
`ifndef SYNTHESIS
    $fwrite(log_fh, " ---   %s\n", "isolde_exec_block::start_gemm");
    $fwrite(log_fh, "  func3=%b\n", isolde_exec_from_decoder.func3);
    $fwrite(log_fh, "    rd1=%d\n", isolde_exec_from_decoder.rd);
    $fwrite(log_fh, "    rs1=%d\n", isolde_exec_from_decoder.rs1);
    $fwrite(log_fh, "    rs2=%d\n", isolde_exec_from_decoder.rs2);
    $fwrite(log_fh, "    rs4=%d\n", isolde_rf_bus.raddr_0 );
    $fwrite(log_fh, "     Q[%d] = [ %d, %d, %d, %d ]\n", isolde_rf_bus.raddr_0, isolde_rf_bus.rdata_0[0], isolde_rf_bus.rdata_0[1],  
                                                                                isolde_rf_bus.rdata_0[2], isolde_rf_bus.rdata_0[3]);
    $fwrite(log_fh, "    rs5=%d\n", isolde_rf_bus.raddr_1 );
    $fwrite(log_fh, "     Q[%d] = [ %d, %d, %d, %d ]\n", isolde_rf_bus.raddr_1, isolde_rf_bus.rdata_1[0], isolde_rf_bus.rdata_1[1],  
                                                                                isolde_rf_bus.rdata_1[2], isolde_rf_bus.rdata_1[3]);
    $fwrite(log_fh, "  funct2=%b\n", isolde_exec_from_decoder.funct2 );                                                                                

`endif
    begin
      cnt_max <= 4;  // wait cycles time for completion
    end
  endtask

  task static start_conv2d;
`ifndef SYNTHESIS
    $fwrite(log_fh, " ---   %s\n", "isolde_exec_block::start_conv2d");
    $fwrite(log_fh, "  func3=%b\n", isolde_exec_from_decoder.func3);
    $fwrite(log_fh, "     rd=%d\n", isolde_exec_from_decoder.rd);
    $fwrite(log_fh, "    rs1=%d\n", isolde_exec_from_decoder.rs1);
    $fwrite(log_fh, "    rs2=%d\n", isolde_exec_from_decoder.rs2);

`endif
    begin
      cnt_max <= 4;  // wait cycles time for completion
    end
  endtask


endmodule
