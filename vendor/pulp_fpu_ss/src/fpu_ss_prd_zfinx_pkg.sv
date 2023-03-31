// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// FPU Predecoder Package
// Contributor: Moritz Imfeld <moimfeld@student.ethz.ch>

package fpu_ss_prd_zfinx_pkg;

// parameter int unsigned NumInstr="NUMBER OF FP INSTR";
parameter int unsigned NumInstr=30;
parameter fpu_ss_pkg::offload_instr_t OffloadInstr[NumInstr] = '{
  '{
    instr_data: 32'b 00000_00_00000_00000_000_00000_1000011, // FMADD.S ok
    instr_mask: 32'b 00000_11_00000_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b111
   }
  },
  '{
    instr_data: 32'b 00000_00_00000_00000_000_00000_1000111, // FMSUB.S ok
    instr_mask: 32'b 00000_11_00000_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b111
    }
  },
  '{
    instr_data: 32'b 00000_00_00000_00000_000_00000_1001011, // FNMSUB.S ok
    instr_mask: 32'b 00000_11_00000_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b111
    }
  },
  '{
    instr_data: 32'b 00000_00_00000_00000_000_00000_1001111, // FNMADD.S ok
    instr_mask: 32'b 00000_11_00000_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b111
    }
  },
  '{
    instr_data: 32'b 0000000_00000_00000_000_00000_1010011, // FADD.S ok
    instr_mask: 32'b 1111111_00000_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 0000100_00000_00000_000_00000_1010011, // FSUB.S ok
    instr_mask: 32'b 1111111_00000_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 0001000_00000_00000_000_00000_1010011, // FMUL.S ok
    instr_mask: 32'b 1111111_00000_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 0001100_00000_00000_000_00000_1010011, // FDIV.S ok
    instr_mask: 32'b 1111111_00000_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 0101100_00000_00000_000_00000_1010011, // FSQRT.S ok
    instr_mask: 32'b 1111111_11111_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 0010000_00000_00000_000_00000_1010011, // FSGNJ.S ok
    instr_mask: 32'b 1111111_00000_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 0010000_00000_00000_001_00000_1010011, // FSGNJN.S ok
    instr_mask: 32'b 1111111_00000_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 0010000_00000_00000_010_00000_1010011, // FSGNJX.S ok
    instr_mask: 32'b 1111111_00000_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 0010100_00000_00000_000_00000_1010011, // FMIN.S
    instr_mask: 32'b 1111111_00000_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 0010100_00000_00000_001_00000_1010011, // FMAX.S
    instr_mask: 32'b 1111111_00000_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 1100000_00000_00000_000_00000_1010011, // FCVT.W.S
    instr_mask: 32'b 1111111_11111_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 1100000_00001_00000_000_00000_1010011, // FCVT.WU.S
    instr_mask: 32'b 1111111_11111_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 1010000_00000_00000_010_00000_1010011, // FEQ.S
    instr_mask: 32'b 1111111_00000_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 1010000_00000_00000_001_00000_1010011, // FLT.S
    instr_mask: 32'b 1111111_00000_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 1010000_00000_00000_000_00000_1010011, // FLE.S
    instr_mask: 32'b 1111111_00000_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b011
    }
  },
  '{
    instr_data: 32'b 1110000_00000_00000_001_00000_1010011, // FCLASS.S
    instr_mask: 32'b 1111111_11111_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 1101000_00000_00000_000_00000_1010011, // FCVT.S.W
    instr_mask: 32'b 1111111_11111_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 1101000_00001_00000_000_00000_1010011, // FCVT.S.WU
    instr_mask: 32'b 1111111_11111_00000_000_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 000000000011_00000_001_00000_1110011, // CSRRW (fscsr) NOTE: two instructions (swap and write)
    instr_mask: 32'b 111111111111_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 000000000011_00000_010_00000_1110011, // CSRRS (frcsr)
    instr_mask: 32'b 111111111111_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 000000000010_00000_001_00000_1110011, // CSRRW (fsrm) NOTE: two instructions (swap and write)
    instr_mask: 32'b 111111111111_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 000000000010_00000_010_00000_1110011, // CSRRS (frrm)
    instr_mask: 32'b 111111111111_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 000000000010_00000_101_00000_1110011, // CSRRWI (fsrmi) NOTE: two instructions (swap and write)
    instr_mask: 32'b 111111111111_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b000
    }
  },
  '{
    instr_data: 32'b 000000000001_00000_001_00000_1110011, // CSRRW (fsflags) NOTE: two instructions (swap and write)
    instr_mask: 32'b 111111111111_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 000000000001_00000_010_00000_1110011, // CSRRS (frflags)
    instr_mask: 32'b 111111111111_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b001
    }
  },
  '{
    instr_data: 32'b 000000000001_00000_101_00000_1110011, // CSRRWI (fsflagsi) NOTE: two instructions (swap and write)
    instr_mask: 32'b 111111111111_00000_111_00000_1111111,
    prd_rsp : '{
      p_accept : 1'b1,
      p_writeback : 1'b1,
      p_is_mem_op : 1'b0,
      p_use_rs : 3'b000
    }
  }
};

endpackage // fpu_ss_prd_zfinx_pkg
