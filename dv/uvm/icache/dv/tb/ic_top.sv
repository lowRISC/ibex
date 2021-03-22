// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module ic_top import ibex_pkg::*; #(parameter bit ICacheECC = 1'b0) (
    input  logic                           clk_i,
    input  logic                           rst_ni,
    input  logic                           req_i,
    input  logic                           branch_i,
    input  logic                           branch_spec_i,
    input  logic                           predicted_branch_i,
    input  logic                           branch_mispredict_i,
    input  logic [31:0]                    addr_i,
    input  logic                           ready_i,
    output logic                           valid_o,
    output logic [31:0]                    rdata_o,
    output logic [31:0]                    addr_o,
    output logic                           err_o,
    output logic                           err_plus2_o,
    output logic                           instr_req_o,
    input  logic                           instr_gnt_i,
    output logic [31:0]                    instr_addr_o,
    input  logic [BUS_SIZE-1:0]            instr_rdata_i,
    input  logic                           instr_err_i,
    input  logic                           instr_pmp_err_i,
    input  logic                           instr_rvalid_i,

    input  logic                           icache_enable_i,
    input  logic                           icache_inval_i,
    output logic                           busy_o
);

  localparam int unsigned BusSizeECC  = ICacheECC ? (BUS_SIZE + 7) : BUS_SIZE;
  localparam int unsigned LineSizeECC = BusSizeECC * IC_LINE_BEATS;
  localparam int unsigned TagSizeECC  = ICacheECC ? (IC_TAG_SIZE + 6) : IC_TAG_SIZE;

  // RAM IO
  logic [IC_NUM_WAYS-1:0]         ic_tag_req;
  logic                           ic_tag_write;
  logic [IC_INDEX_W-1:0]          ic_tag_addr;
  logic [TagSizeECC-1:0]          ic_tag_wdata;
  logic [TagSizeECC-1:0]          ic_tag_rdata [IC_NUM_WAYS];
  logic [IC_NUM_WAYS-1:0]         ic_data_req;
  logic                           ic_data_write;
  logic [IC_INDEX_W-1:0]          ic_data_addr;
  logic [LineSizeECC-1:0]         ic_data_wdata;
  logic [LineSizeECC-1:0]         ic_data_rdata [IC_NUM_WAYS];

  // DUT
  ibex_icache #(
      .ICacheECC       (ICacheECC),
      .BusSizeECC      (BusSizeECC),
      .TagSizeECC      (TagSizeECC),
      .LineSizeECC     (LineSizeECC)
  ) icache_i (
      .clk_i               ( clk_i                      ),
      .rst_ni              ( rst_ni                     ),

      .req_i               ( req_i                      ),

      .branch_i            ( branch_i                   ),
      .branch_spec_i       ( branch_spec_i              ),
      .predicted_branch_i  ( predicted_branch_i         ),
      .branch_mispredict_i ( branch_mispredict_i        ),
      .addr_i              ( addr_i                     ),

      .ready_i             ( ready_i                    ),
      .valid_o             ( valid_o                    ),
      .rdata_o             ( rdata_o                    ),
      .addr_o              ( addr_o                     ),
      .err_o               ( err_o                      ),
      .err_plus2_o         ( err_plus2_o                ),

      .instr_req_o         ( instr_req_o                ),
      .instr_addr_o        ( instr_addr_o               ),
      .instr_gnt_i         ( instr_gnt_i                ),
      .instr_rvalid_i      ( instr_rvalid_i             ),
      .instr_rdata_i       ( instr_rdata_i              ),
      .instr_err_i         ( instr_err_i                ),
      .instr_pmp_err_i     ( instr_pmp_err_i            ),

      .ic_tag_req_o        ( ic_tag_req                 ),
      .ic_tag_write_o      ( ic_tag_write               ),
      .ic_tag_addr_o       ( ic_tag_addr                ),
      .ic_tag_wdata_o      ( ic_tag_wdata               ),
      .ic_tag_rdata_i      ( ic_tag_rdata               ),
      .ic_data_req_o       ( ic_data_req                ),
      .ic_data_write_o     ( ic_data_write              ),
      .ic_data_addr_o      ( ic_data_addr               ),
      .ic_data_wdata_o     ( ic_data_wdata              ),
      .ic_data_rdata_i     ( ic_data_rdata              ),

      .icache_enable_i     ( icache_enable_i            ),
      .icache_inval_i      ( icache_inval_i             ),
      .busy_o              ( busy_o                     )
  );
  // RAMs
  for (genvar way = 0; way < IC_NUM_WAYS; way++) begin : gen_rams
    // Tag RAM instantiation
    prim_ram_1p #(
      .Width           (TagSizeECC),
      .Depth           (IC_NUM_LINES),
      .DataBitsPerMask (TagSizeECC)
    ) tag_bank (
      .clk_i    (clk_i),
      .req_i    (ic_tag_req[way]),
      .cfg_i    ('0),
      .write_i  (ic_tag_write),
      .wmask_i  ({TagSizeECC{1'b1}}),
      .addr_i   (ic_tag_addr),
      .wdata_i  (ic_tag_wdata),
      .rdata_o  (ic_tag_rdata[way])
    );
    // Data RAM instantiation
    prim_ram_1p #(
      .Width           (LineSizeECC),
      .Depth           (IC_NUM_LINES),
      .DataBitsPerMask (LineSizeECC)
    ) data_bank (
      .clk_i    (clk_i),
      .req_i    (ic_data_req[way]),
      .cfg_i    ('0),
      .write_i  (ic_data_write),
      .wmask_i  ({LineSizeECC{1'b1}}),
      .addr_i   (ic_data_addr),
      .wdata_i  (ic_data_wdata),
      .rdata_o  (ic_data_rdata[way])
    );
  end

endmodule
