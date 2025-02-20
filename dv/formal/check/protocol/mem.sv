// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
The following describes the protocol for the memory interface to Ibex, as defined by the documentation.

In this case all responses must be within bounded time (`TIME_BOUND cycles). Removing the bound
leaves some properties inconclusive.
*/

// Sail does not specify these I don't think
NoDataErr: assume property (~data_err_i);
NoInstrErr: assume property (~instr_err_i);
`define TIME_LIMIT 5

interface mem_assume_t(
    input logic req_o,
    input logic gnt_i,
    input logic rvalid_i
);
    logic [7:0] outstanding_reqs_q;
    logic [7:0] outstanding_reqs;
    assign outstanding_reqs = outstanding_reqs_q + gnt_i - rvalid_i;

    always @(posedge clk_i or negedge rst_ni) begin
        outstanding_reqs_q <= rst_ni ? outstanding_reqs : 0;
    end

    // 1. Only send an rvalid if there is an outstanding request, but not in this cycle
    MemValidBounded: assume property (outstanding_reqs_q == 8'b0 |-> ~rvalid_i);
    // 2. Grants can only be sent when they are requested
    MemGntOnRequest: assume property (~req_o |-> ~gnt_i);

    // Grants must respond within TIME_LIMIT cycles
    GntBound: assume property (req_o |-> ##[0:`TIME_LIMIT] gnt_i);

    // RValid takes no more than TIME_LIMIT cycles
    MemValidTimer: assume property (outstanding_reqs != 0 |-> ##[0:`TIME_LIMIT] rvalid_i);

    // Responses have to come eventually, implied by the above bounds so removed
    // MemGntEventually: assume property (req_o |-> s_eventually gnt_i);
    // MemRespEventually: assume property (always (s_eventually (outstanding_reqs == 8'b0)));
endinterface

mem_assume_t instr_mem_assume(instr_req_o, instr_gnt_i, instr_rvalid_i);
mem_assume_t data_mem_assume(data_req_o, data_gnt_i, data_rvalid_i);
