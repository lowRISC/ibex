class ISOLDEOps <string name,bits<7> _opcode , bits<7> _funct7> {
  string Name = name;
  bits<7> funct7 = _funct7;
  bits<7> opcode = _opcode;
}
//160 bit
def ISOLDE_LOAD            : ISOLDEOps<"LDQword",         OPC_160BIT.Value,    0b0000011>;
//96 bit 
def ISOLDE_CONV2D_EX       : ISOLDEOps<"CONV2DExInstr",    OPC_96BIT.Value,     0b0000000>;
//64 bit 
def ISOLDE_GEMM            : ISOLDEOps<"GEMMInstr",       OPC_64BIT.Value,     0b0000111>;

//
// 64 bit custom
//

class ISOLDEInst64< 
                     dag outs, dag ins, 
                     list<dag> pattern >
    : Instruction {
  field bits<64> Inst;
  // SoftFail is a field the disassembler can use to provide a way for
  // instructions to not match without killing the whole decode process. It is
  // mainly used for ARM, but Tablegen expects this field to exist or it fails
  // to build the decode table. Must have the same size as Inst
  field bits<64> SoftFail = 0;
  let Size = 8; //number of bytes
  let TSFlags{4-0} = InstFormat64bit.Value;

  let Namespace = "RISCV";
  let OutOperandList = outs;
  let InOperandList = ins;  
  let Pattern = pattern;

  let Inst{6-0} = OPC_64BIT.Value;
}

class ISOLDE64Base< bits<7> _funct7, bits<3> _funct3, bits<3> _ext_funct3,dag outs, dag ins, string opcodestr, string dt, string argstr, 
            list<dag> pattern>
            : ISOLDEInst64< outs, ins, pattern >{
  let AsmString = !strconcat(opcodestr, ".", dt, "\t", argstr);
  //let AsmString = opcodestr # "\t" # argstr;
  //let isPseudo = 1;
  
  bits<5>  rd1;
  bits<3>  funct3 = _funct3;
  bits<5>  rs1;
  bits<5>  rs2;
  bits<7>  funct7 =_funct7;
//extension
  bits<5>  rd2;
  bits<5>  rs3;
  bits<5>  rs4;
  bits<5>  rs5;
  bits<5>  rs6;

  //first 32 bits
  let Inst{31-25} = funct7; 
  let Inst{24-20} = rs2; 
  let Inst{19-15} = rs1; 
  let Inst{14-12} = funct3;
  let Inst{11-7} = rd1;
  //Inst{6-0} equals OPC_64BIT.Value, already set in ISOLDEInst64
//extension
  let Inst{63-62} = 0b00;
  let Inst{61-57} = rs6;
  let Inst{56-52} = rs5;
  let Inst{51-47} = rs4;
  let Inst{46-44} = _ext_funct3; 
  let Inst{43-39} = rd2;
  let Inst{38-37} = 0b00;
  let Inst{36-32} = rs3;
}


class ONNXBase< bits<7> _funct7, bits<3> _funct3,dag outs, dag ins, string opcodestr, string dt, string argstr, 
            list<dag> pattern>:ISOLDE64Base<  _funct7, _funct3, 0b000, outs,  ins,  opcodestr,  dt,  argstr,  pattern>;


//
//96
//
class ISOLDEInst96< 
                     dag outs, dag ins, 
                     list<dag> pattern >
    : Instruction {
  field bits<96> Inst;
  // SoftFail is a field the disassembler can use to provide a way for
  // instructions to not match without killing the whole decode process. It is
  // mainly used for ARM, but Tablegen expects this field to exist or it fails
  // to build the decode table.
  field bits<96> SoftFail = 0;
  let Size = 12; //number of bytes
  let TSFlags{4-0} = InstFormat96bit.Value;

  let Namespace = "RISCV";
  let OutOperandList = outs;
  let InOperandList = ins;  
  let Pattern = pattern;

  let Inst{6-0} = OPC_96BIT.Value;
  let Inst{14-12} = 0b001; //nnn=b001
}

class ISOLDEInst96R< bits<7> _funct7, bits<3> _funct3, bits<3> _ext_funct3,dag outs, dag ins, string opcodestr, string dt, string argstr, 
            list<dag> pattern>
            : ISOLDEInst96< outs, ins, pattern >{
  let AsmString = !strconcat(opcodestr, ".", dt, "\t", argstr);
  
  bits<5>  rd1;
  bits<3>  funct3 = _funct3;
  bits<5>  rs1;
  bits<5>  rs2;
  bits<7>  funct7 =_funct7;
//extension 1st word
  bits<5>  rd2;
  bits<5>  rs3;
  bits<5>  rs4;
  bits<5>  rs5;
  bits<5>  rs6;
//extension 2nd word
  bits<5>  rd3;
  bits<5>  rs7;
  bits<5>  rs8;
  bits<5>  rs9;
  bits<5>  rs10;


  //first 32 bits
  let Inst{31-25} = funct7; 
  let Inst{24-20} = rs2; 
  let Inst{19-15} = rs1; 
  // Inst{14-12} equals b001, already set in ISOLDEInst96
  let Inst{11-7} = rd1;
  //Inst{6-0} equals OPC_96BIT.Value, already set in ISOLDEInst96
  //
  let Inst{63-62} = 0b00;
  let Inst{61-57} = rs6;
  let Inst{56-52} = rs5;
  let Inst{51-47} = rs4;
  let Inst{46-44} = _funct3; 
  let Inst{43-39} = rd2;
  let Inst{38-37} = 0b00;
  let Inst{36-32} = rs3;
  //
  let Inst{95-94} = 0b00;
  let Inst{93-89} = rs10;
  let Inst{88-84} = rs9;
  let Inst{83-79} = rs8;
  let Inst{78-76} = _ext_funct3; 
  let Inst{75-71} = rd3;
  let Inst{70-69} = 0b00;
  let Inst{68-64} = rs7;
}            

//https://onnx.ai/onnx/operators/onnx__Gemm.html
class GEMMInstr < bits<3> funct3
                ,string Dt 
                ,SDPatternOperator IntOp >
    : ONNXBase <  ISOLDE_GEMM.funct7,
                  funct3,
                  (outs QPR:$rd2), 
                  (ins GPR:$rd1, GPR:$rs1, QPR:$rs4, GPR:$rs2, QPR:$rs5, GPR:$rs3, i32imm:$transA, i32imm:$transB),
                  "gemm",Dt, 
                  "$rd1, $rd2, $rs1, $rs4, $rs2, $rs5, $rs3, $transA, $transB",
                  [
                    ( set 
                      
                        (v4i32 QPR:$rd2),  ( IntOp   (  iPTR  GPR:$rd1)
                                                  ,(  iPTR     GPR:$rs1)
                                                  ,(  v4i32    QPR:$rs4)
                                                  ,(  iPTR     GPR:$rs2)
                                                  ,(  v4i32    QPR:$rs5)
                                                  ,(  iPTR     GPR:$rs3)
                                                  ,(  i32       imm:$transA)
                                                  ,(  i32       imm:$transB)
                                                  
                          
                          )
                    )
                    
                  ]
                >
                {
  //
  bits<32>  transA;
  bits<32>  transB;
  let Inst{38} = transA{0};
  let Inst{37} = transB{0};
  let rs6 = 0b00000; //it should hold alpha and beta paramaeters, f32 format
  let hasSideEffects = true;
  let mayLoad = true;
  let mayStore = true;
}


class CONV2DExInstr < bits<3> funct3
                ,string Dt 
                ,SDPatternOperator IntOp >
    : ISOLDEInst96R <  ISOLDE_CONV2D_EX.funct7,
                  funct3,
                  0b000,
                  (outs QPR:$rd2), 
                  (ins GPR:$rd1, GPR:$rs1, QPR:$rs4, GPR:$rs2, QPR:$rs5, QPR:$rs3, QPR:$rs6, GPR:$rs7),
                  "conv2dex",Dt, 
                  "$rd1, $rd2, $rs1, $rs4, $rs2, $rs5, $rs3, $rs6, $rs7",
                  [
                    ( set 
                      
                        (v4i32 QPR:$rd2),  ( IntOp (  iPTR     GPR:$rd1)
                                                  ,(  iPTR     GPR:$rs1)
                                                  ,(  v4i32    QPR:$rs4)
                                                  ,(  iPTR     GPR:$rs2)
                                                  ,(  v4i32    QPR:$rs5)
                                                  ,(  v4i32    QPR:$rs3)
                                                  ,(  v4i32    QPR:$rs6)
                                                  ,(  iPTR     GPR:$rs7)
                          
                          )
                    )
                    
                  ]
                >
                {

  let rd3  = 0b00000;
  let rs8  = 0b00000;
  let rs9  = 0b00000;
  let rs10 = 0b00000;
  //
  let hasSideEffects = true;
  let mayLoad = true;
  //let mayStore = true;
}
