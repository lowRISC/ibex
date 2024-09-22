// Copyleft

module isolde_exec_block
  import isolde_decoder_pkg::*;
(
           isolde_fetch2exec_if isolde_exec_from_decoder,
    output logic                isolde_exec_busy_o
);

  logic clk;
  logic g_rst_n;
  logic start_exec;

  logic [2:0] cnt, cnt_max;


  // FSM states
  typedef enum logic [1:0] {
    IDLE,
    START,  //start execution
    WAIT    //wait for completion
  } state_t;

  state_t ievli_state, ievli_next;

  assign clk = isolde_exec_from_decoder.clk_i;
  assign g_rst_n = isolde_exec_from_decoder.rst_ni;
  //assign start_exec = (isolde_exec_from_decoder.isolde_decoder_enable & isolde_exec_from_decoder.isolde_decoder_ready);
  assign start_exec = isolde_exec_from_decoder.isolde_decoder_ready;
  assign isolde_exec_from_decoder.stall_isolde_decoder = isolde_exec_busy_o;

  always_ff @(posedge clk or negedge g_rst_n) begin
    if (!g_rst_n) begin
      cnt <= 0;
      ievli_state <= IDLE;
    end else begin
      ievli_state <= ievli_next;
      case (ievli_next)
        START: begin
          cnt <= 1;
          cnt_max <= 4;  //dummy value
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

endmodule
