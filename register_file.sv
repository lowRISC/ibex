module riscv_register_file
#(
  parameter ADDR_WIDTH    = 5,
  parameter DATA_WIDTH    = 32
)
(
  // Clock and Reset
  input  logic                   clk,
  input  logic                   rst_n,

  input  logic                   test_en_i,

  //Read port R1
  input  logic [ADDR_WIDTH-1:0]  raddr_a_i,
  output logic [DATA_WIDTH-1:0]  rdata_a_o,

  //Read port R2
  input  logic [ADDR_WIDTH-1:0]  raddr_b_i,
  output logic [DATA_WIDTH-1:0]  rdata_b_o,

  //Read port R3
  input  logic [ADDR_WIDTH-1:0]  raddr_c_i,
  output logic [DATA_WIDTH-1:0]  rdata_c_o,

  // Write port W1
  input  logic [ADDR_WIDTH-1:0]   waddr_a_i,
  input  logic [DATA_WIDTH-1:0]   wdata_a_i,
  input  logic                    we_a_i,

  // Write port W2
  input  logic [ADDR_WIDTH-1:0]   waddr_b_i,
  input  logic [DATA_WIDTH-1:0]   wdata_b_i,
  input  logic                    we_b_i
);

  localparam    NUM_WORDS = 2**ADDR_WIDTH;

  logic [DATA_WIDTH-1:0]      MemContentxDP[NUM_WORDS];

  logic [NUM_WORDS-1:1]       WAddrOneHotxDa;
  logic [NUM_WORDS-1:1]       WAddrOneHotxDb;
  logic [NUM_WORDS-1:1]       WAddrOneHotxDb_reg;

  logic [NUM_WORDS-1:1]       ClocksxC;
  logic [DATA_WIDTH-1:0]      WDataIntxDa;
  logic [DATA_WIDTH-1:0]      WDataIntxDb;

  logic clk_int;

  logic we_int;

  int unsigned i;
  int unsigned j;
  int unsigned k;

  genvar x;
  genvar y;

  assign we_int = we_a_i | we_b_i;

  cluster_clock_gating CG_WE_GLOBAL
  (
    .clk_i     ( clk       ),
    .en_i      ( we_int    ),
    .test_en_i ( test_en_i ),
    .clk_o     ( clk_int   )
  );

  //-----------------------------------------------------------------------------
  //-- READ : Read address decoder RAD
  //-----------------------------------------------------------------------------
  assign rdata_a_o = MemContentxDP[raddr_a_i];
  assign rdata_b_o = MemContentxDP[raddr_b_i];
  assign rdata_c_o = MemContentxDP[raddr_c_i];

  //-----------------------------------------------------------------------------
  //-- WRITE : Write Address Decoder (WAD), combinatorial process
  //-----------------------------------------------------------------------------
    always_comb
    begin : p_WADa
      for(i=1; i<NUM_WORDS; i++)
      begin : p_WordItera
        if ( (we_a_i == 1'b1 ) && (waddr_a_i == i) )
          WAddrOneHotxDa[i] = 1'b1;
        else
          WAddrOneHotxDa[i] = 1'b0;
      end
    end

    always_comb
    begin : p_WADb
      for(j=1; j<NUM_WORDS; j++)
      begin : p_WordIterb
        if ( (we_b_i == 1'b1 ) && (waddr_b_i == j) )
          WAddrOneHotxDb[j] = 1'b1;
        else
          WAddrOneHotxDb[j] = 1'b0;
      end
    end

    always_ff @(posedge clk_int)
    begin
      if(we_a_i | we_b_i)
        WAddrOneHotxDb_reg <= WAddrOneHotxDb;
    end

  //-----------------------------------------------------------------------------
  //-- WRITE : Clock gating (if integrated clock-gating cells are available)
  //-----------------------------------------------------------------------------
  generate
    for(x=1; x<NUM_WORDS; x++)
    begin : CG_CELL_WORD_ITER
      cluster_clock_gating CG_Inst
      (
        .clk_i     ( clk_int                               ),
        .en_i      ( WAddrOneHotxDa[x] | WAddrOneHotxDb[x] ),
        .test_en_i ( test_en_i                             ),
        .clk_o     ( ClocksxC[x]                           )
      );
    end
  endgenerate

  //-----------------------------------------------------------------------------
  // WRITE : SAMPLE INPUT DATA
  //---------------------------------------------------------------------------
  always_ff @(posedge clk)
  begin : sample_waddr
    if(we_a_i)
      WDataIntxDa <= wdata_a_i;
    if(we_b_i)
      WDataIntxDb <= wdata_b_i;
  end

  //-----------------------------------------------------------------------------
  //-- WRITE : Write operation
  //-----------------------------------------------------------------------------
  //-- Generate M = WORDS sequential processes, each of which describes one
  //-- word of the memory. The processes are synchronized with the clocks
  //-- ClocksxC(i), i = 0, 1, ..., M-1
  //-- Use active low, i.e. transparent on low latches as storage elements
  //-- Data is sampled on rising clock edge

  always_latch
  begin : latch_wdata
    // Note: The assignment has to be done inside this process or Modelsim complains about it
    MemContentxDP[0] = 32'b0;

    for(k=1; k<NUM_WORDS; k++)
    begin : w_WordIter
      if(ClocksxC[k] == 1'b1)
        MemContentxDP[k] = WAddrOneHotxDb_reg[k] ? WDataIntxDb : WDataIntxDa;
    end
  end


endmodule
