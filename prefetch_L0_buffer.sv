////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                 DEI @ UNIBO - University of Bologna                        //
//                                                                            //
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Create Date:    06/08/2014                                                 //
// Design Name:    RISC-V processor core                                      //
// Module Name:    prefetch_buffer.sv                                         //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch Buffer that caches instructions. This cuts overly //
//                 long critical paths to the instruction cache               //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module prefetch_L0_buffer
#(
  parameter                                   RDATA_IN_WIDTH = 128
)
(
  input  logic                                clk,
  input  logic                                rst_n,

  input  logic                                req_i,
  input  logic                                branch_i,
  input  logic                                ready_i,
  input  logic [31:0]                         addr_i,

  output logic                                valid_o,
  output logic [31:0]                         rdata_o,
  output logic [31:0]                         addr_o,

  output logic                                unaligned_valid_o,
  output logic [31:0]                         unaligned_rdata_o,

  // goes to instruction memory / instruction cache
  output logic                                instr_req_o,
  output logic [31:0]                         instr_addr_o,
  input  logic                                instr_gnt_i,
  input  logic                                instr_rvalid_i,
  input  logic [RDATA_IN_WIDTH/32-1:0][31:0]  instr_rdata_i,

  // Prefetch Buffer Status
  output logic                                busy_o
);

  enum logic [2:0] {EMPTY, VALID_L0, WAIT_GNT, WAIT_RVALID, WAIT_ABORTED } CS, NS;
  logic [31:0]        current_address;
  logic [1:0]         pointer_cs, pointer_ns;
  logic               update_current_address;

  logic [3:0][31:0]   L0_buffer;
  logic               valid_L0_buffer;
  logic [15:0]        previous_chunk;
  logic               valid_previous_chunk;
  logic               clear_buffer;


  assign busy_o = (CS != EMPTY);


  always_ff @(posedge clk or negedge rst_n)
  begin
    if(~rst_n)
    begin
      CS               <= EMPTY;
      current_address  <= '0;
      pointer_cs       <= '0;
    end
    else
    begin
      CS <= NS;

      if(branch_i)
      begin
        current_address <= {addr_i[31:4],4'b0000};
        pointer_cs <= addr_i[3:2];
      end
      else
      begin
        if(update_current_address)
          current_address <= current_address + 5'h10; // jump to the next cache line

        pointer_cs <= pointer_ns;
      end
    end
  end



  always_comb
  begin
    valid_o                 = 1'b0;
    addr_o                  = current_address + (pointer_cs<<2);
    pointer_ns              = pointer_cs;
    instr_req_o             = 1'b0;
    instr_addr_o            = (branch_i) ? addr_i : current_address + 5'h10;
    update_current_address  = 1'b0;
    rdata_o                 = instr_rdata_i[pointer_cs];
    clear_buffer            = 1'b0;

    case(addr_o[3:2])
       2'b00: begin unaligned_rdata_o       = {L0_buffer[0][15:0], previous_chunk     };    unaligned_valid_o       = valid_previous_chunk;  end
       2'b01: begin unaligned_rdata_o       = {L0_buffer[1][15:0], L0_buffer[0][31:16] };   unaligned_valid_o       = valid_o;               end
       2'b10: begin unaligned_rdata_o       = {L0_buffer[2][15:0], L0_buffer[1][31:16] };   unaligned_valid_o       = valid_o;               end
       2'b11: begin unaligned_rdata_o       = {L0_buffer[3][15:0], L0_buffer[2][31:16] };   unaligned_valid_o       = valid_o;               end
    endcase // addr_o


    case(CS)

      EMPTY:
      begin
        instr_req_o = branch_i;
        if(branch_i) // make the request to icache
        begin

          if(instr_gnt_i)
          begin
            NS = WAIT_RVALID;
          end
          else
          begin
            NS = WAIT_GNT;
          end
        end
        else
        begin
          NS = EMPTY;
        end
      end //~EMPTY

      WAIT_RVALID:
      begin
        if(branch_i) // there is a pending branch
        begin
          if(instr_rvalid_i)
          begin
            instr_req_o  = 1'b1;
            instr_addr_o = {addr_i[31:4],4'b0000};

            if(instr_gnt_i)
            begin
              NS = WAIT_RVALID;
            end
            else
            begin
              NS = WAIT_GNT;
            end
          end
          else
          begin
            NS = WAIT_ABORTED;
          end

        end
        else // else (branch_i)
        begin
          valid_o             = instr_rvalid_i;

          case(pointer_cs)
            2'b00:
            begin
              unaligned_rdata_o   = { instr_rdata_i[0][15:0], L0_buffer[3][31:16]  };
              if(valid_L0_buffer)
              begin
                unaligned_valid_o       = instr_rvalid_i;
              end
              else
              begin
                unaligned_valid_o       = 1'b0;
              end
            end

            2'b01: begin unaligned_rdata_o       = {instr_rdata_i[1][15:0], instr_rdata_i[0][31:16] };   unaligned_valid_o       = instr_rvalid_i;  end
            2'b10: begin unaligned_rdata_o       = {instr_rdata_i[2][15:0], instr_rdata_i[1][31:16] };   unaligned_valid_o       = instr_rvalid_i;  end
            2'b11: begin unaligned_rdata_o       = {instr_rdata_i[3][15:0], instr_rdata_i[2][31:16] };   unaligned_valid_o       = instr_rvalid_i;  end
          endcase // pointer_cs

          if(instr_rvalid_i)
          begin

            if(&pointer_cs) // we are receiving the last packet, then prefetch the next one
            begin

              if(ready_i)
              begin
                instr_req_o  = 1'b1; //if the cpu is ready to sample the instruction, then ask for a new instruction
                instr_addr_o = current_address + 5'h10;
                pointer_ns = '0;
                update_current_address = 1'b1;

                if(instr_gnt_i)
                begin
                  NS = WAIT_RVALID;
                end
                else
                begin
                  NS = WAIT_GNT;
                end
              end
              else
              begin
                NS = VALID_L0;
              end
            end
            else // not the last chunk
            begin
              NS = VALID_L0;
              if(ready_i)
              begin
                pointer_ns = pointer_cs + 1'b1;
              end
              else
              begin
                pointer_ns = pointer_cs;
              end
            end
          end
          else // still wait instr_rvalid_i
          begin
            NS = WAIT_RVALID;
          end
        end
      end //~WAIT_RVALID

     VALID_L0:
     begin
        valid_o = 1'b1;
        rdata_o = L0_buffer[pointer_cs];
        case(pointer_cs)
          2'b00: begin unaligned_rdata_o       = {L0_buffer[0][15:0], previous_chunk      };   unaligned_valid_o       = valid_previous_chunk;  end
          2'b01: begin unaligned_rdata_o       = {L0_buffer[1][15:0], L0_buffer[0][31:16] };   unaligned_valid_o       = 1'b1;  end
          2'b10: begin unaligned_rdata_o       = {L0_buffer[2][15:0], L0_buffer[1][31:16] };   unaligned_valid_o       = 1'b1;  end
          2'b11: begin unaligned_rdata_o       = {L0_buffer[3][15:0], L0_buffer[2][31:16] };   unaligned_valid_o       = 1'b1;  end
        endcase // pointer_cs


        if(branch_i)
        begin
          instr_req_o  = 1'b1;
          instr_addr_o = {addr_i[31:4],4'b0000};
          if(instr_gnt_i)
          begin
            NS = WAIT_RVALID;
          end
          else
          begin
            NS = WAIT_GNT;
          end
        end
        else
        begin
          if(ready_i)
          begin
            if( &pointer_cs ) // we are dispathing the last packet, therefore prefetch the next cache line
            begin
              instr_req_o = 1'b1;
              instr_addr_o = current_address + 5'h10;
              update_current_address = 1'b1;
              pointer_ns = '0;

              if(instr_gnt_i)
              begin
                NS = WAIT_RVALID;
              end
              else
              begin
                NS = WAIT_GNT;
              end
            end
            else
            begin
              pointer_ns = pointer_cs + 1'b1;
              NS = VALID_L0;
            end
          end
          else // not ready, stay here!!!!
          begin
            NS = VALID_L0;
          end
        end
     end //~VALID_L0

      WAIT_GNT:
      begin
        if(branch_i)
        begin
          instr_req_o  = 1'b1;
          instr_addr_o = {addr_i[31:4],4'b0000};

          if(instr_gnt_i)
          begin
            NS = WAIT_RVALID;
          end
          else
          begin
            NS = WAIT_GNT;
          end
        end
        else
        begin
          instr_req_o = 1'b1;
          instr_addr_o = current_address; // has been previously updated

          if(instr_gnt_i)
          begin
            NS = WAIT_RVALID;
          end
          else
          begin
            NS = WAIT_GNT;
          end
        end
      end //~WAIT_GNT

      WAIT_ABORTED:
      begin
         clear_buffer = 1'b1;
         if(instr_rvalid_i)
         begin
           instr_req_o  = 1'b1;
           instr_addr_o = current_address;

           if(instr_gnt_i)
           begin
             NS = WAIT_RVALID;
           end
           else
           begin
             NS = WAIT_GNT;
           end
         end
         else
         begin
           NS = WAIT_ABORTED;
         end
      end //~WAIT_ABORTED


      default:
      begin
         NS = EMPTY;
         clear_buffer = 1'b1;
      end
    endcase //~CS
  end


  always_ff @(posedge clk or negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      valid_L0_buffer      <= 1'b0;
      L0_buffer            <= '0;
      previous_chunk       <= '0;
      valid_previous_chunk <= 1'b0;
    end
    else
    begin
      if(branch_i || clear_buffer)
      begin
        valid_L0_buffer      <= 1'b0;
        valid_previous_chunk <= 1'b0;
      end
      else
      begin
        if(instr_rvalid_i)
        begin
          L0_buffer       <= instr_rdata_i;
          valid_L0_buffer <= 1'b1;

          if(valid_L0_buffer )
          begin
            valid_previous_chunk <= 1'b1;
            previous_chunk       <= L0_buffer[3][31:16];
          end
        end
      end
    end
  end

endmodule // prefetch_L0_buffer
