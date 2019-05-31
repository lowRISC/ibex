"""
Copyright 2019 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Convert ovpsim sim log to standard riscv instruction trace format
"""
import re
import argparse

from riscv_trace_csv import *

def compare_trace_csv(csv1, csv2, name1, name2):
  """Compare two trace CSV file"""
  matched_cnt = 0
  mismatch_cnt = 0
  gpr_val_1 = {}
  gpr_val_2 = {}

  with open(csv1, "r") as fd1, open(csv2, "r") as fd2:
    instr_trace_1 = []
    instr_trace_2 = []
    trace_csv_1 = RiscvInstructiontTraceCsv(fd1)
    trace_csv_2 = RiscvInstructiontTraceCsv(fd2)
    trace_csv_1.read_trace(instr_trace_1)
    trace_csv_2.read_trace(instr_trace_2)
    trace_1_index = 0
    trace_2_index = 0
    for trace in instr_trace_1:
      trace_1_index += 1
      # Check if there's a GPR change caused by this instruction
      gpr_state_change_1 = check_update_gpr(trace.rd, trace.rd_val, gpr_val_1)
      if gpr_state_change_1 == 0:
        continue
      # Move forward the other trace until a GPR update happens
      gpr_state_change_2 = 0
      while (gpr_state_change_2 == 0 and trace_2_index < len(instr_trace_2)):
        gpr_state_change_2 = check_update_gpr(
                             instr_trace_2[trace_2_index].rd,
                             instr_trace_2[trace_2_index].rd_val,
                             gpr_val_2)
        trace_2_index += 1
      # Check if the GPR update is the same between trace 1 and 2
      if gpr_state_change_2 == 0:
        mismatch_cnt += 1
        print("Mismatch[%d]:\n[%d] %s : %s -> %s(0x%s) addr:0x%s" %
              (mismatch_cnt, trace_1_index, name1, trace.instr_str, trace.rd,
               trace.rd_val, trace.addr))
        print ("%0d instructions left in trace %0s" %
               (len(instr_trace_1) - trace_1_index + 1, name1))
      elif (trace.rd != instr_trace_2[trace_2_index-1].rd or
            trace.rd_val != instr_trace_2[trace_2_index-1].rd_val):
        mismatch_cnt += 1
        # print first 5 mismatches
        if mismatch_cnt <= 5:
          print("Mismatch[%d]:\n[%d] %s : %s -> %s(0x%s) addr:0x%s" %
                (mismatch_cnt, trace_2_index - 1, name1, trace.instr_str,
                 trace.rd, trace.rd_val, trace.addr))
          print("[%d] %s : %s -> %s(0x%s) addr:0x%s" %
                (trace_2_index - 1, name2,
                 instr_trace_2[trace_2_index-1].instr_str,
                 instr_trace_2[trace_2_index-1].rd,
                 instr_trace_2[trace_2_index-1].rd_val,
                 instr_trace_2[trace_2_index-1].addr))
      else:
        matched_cnt += 1
      # Break the loop if it reaches the end of trace 2
      if trace_2_index == len(instr_trace_2):
        break
    # Check if there's remaining instruction that change architectural state
    if trace_2_index != len(instr_trace_2):
      while (trace_2_index < len(instr_trace_2)):
        gpr_state_change_2 = check_update_gpr(
                             instr_trace_2[trace_2_index].rd,
                             instr_trace_2[trace_2_index].rd_val,
                             gpr_val_2)
        if gpr_state_change_2 == 1:
          print ("%0d instructions left in trace %0s" %
                (len(instr_trace_2) - trace_2_index, name2))
          mismatch_cnt += len(instr_trace_2) - trace_2_index
          break
        trace_2_index += 1
    if mismatch_cnt == 0:
      compare_result = "PASSED"
    else:
      compare_result = "FAILED"
    print("Compare result[%s]: %d matched, %d mismatch" %
          (compare_result, matched_cnt, mismatch_cnt))


def check_update_gpr(rd, rd_val, gpr):
  gpr_state_change = 0
  if rd in gpr:
    if rd_val != gpr[rd]:
      gpr_state_change = 1
  else:
    if int(rd_val, 16) != 0:
      gpr_state_change = 1
  gpr[rd] = rd_val
  return gpr_state_change


# Parse input arguments
parser = argparse.ArgumentParser()
parser.add_argument("csv_file_1", type=str, help="Instruction trace 1 CSV")
parser.add_argument("csv_file_2", type=str, help="Instruction trace 2 CSV")
parser.add_argument("csv_name_1", type=str, help="Instruction trace 1 name")
parser.add_argument("csv_name_2", type=str, help="Instruction trace 2 name")
args = parser.parse_args()
# Process ovpsim csv
compare_trace_csv(args.csv_file_1, args.csv_file_2,
                  args.csv_name_1, args.csv_name_2)
