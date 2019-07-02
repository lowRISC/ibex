// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface irq_if;
  logic       clock;
  logic       reset;
  logic       irq_i;
  logic [4:0] irq_id_i;
  logic [4:0] irq_id_o;
  logic       irq_ack_o;
endinterface
