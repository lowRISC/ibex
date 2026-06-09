/*
 * Copyright 2020 Google LLC
 * Copyright 2023 Frontgrade Gaisler
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

`DEFINE_ZCB_INSTR(C_LBU,    CLB_FORMAT,  LOAD,       RV32ZCB, UIMM)
`DEFINE_ZCB_INSTR(C_LHU,    CLH_FORMAT,  LOAD,       RV32ZCB, UIMM)
`DEFINE_ZCB_INSTR(C_LH,     CLH_FORMAT,  LOAD,       RV32ZCB, UIMM)
`DEFINE_ZCB_INSTR(C_SB,     CSB_FORMAT,  STORE,      RV32ZCB, UIMM)
`DEFINE_ZCB_INSTR(C_SH,     CSH_FORMAT,  STORE,      RV32ZCB, UIMM)
`DEFINE_ZCB_INSTR(C_ZEXT_B, CU_FORMAT, ARITHMETIC, RV32ZCB)
`DEFINE_ZCB_INSTR(C_SEXT_B, CU_FORMAT, ARITHMETIC, RV32ZCB)
`DEFINE_ZCB_INSTR(C_ZEXT_H, CU_FORMAT, ARITHMETIC, RV32ZCB)
`DEFINE_ZCB_INSTR(C_SEXT_H, CU_FORMAT, ARITHMETIC, RV32ZCB)
`DEFINE_ZCB_INSTR(C_NOT,    CU_FORMAT, LOGICAL,    RV32ZCB)
`DEFINE_ZCB_INSTR(C_MUL,    CA_FORMAT,   ARITHMETIC, RV32ZCB)

