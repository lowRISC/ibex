/*
*
*

GSoC first code:   // #REVIEW_REQ: Check if all the below comments should stay or be removed. 

This file is still initial: 

The following assumptions are made on the top of the published trace specs at:

* RISC-V Trace Encoder according to riscv-trace-spec doc 
*The doc version is written as:
..............................................................
************ Specs doc RISC-V Processor Trace ****************
Version 1.0
4d009c4de4c68d547adb4adec307a438feb3d815
Gajinder Panesar, Iain Robertson
<gajinder.panesar@ultrasoc.com>, <iain.robertson@ultrasoc.com>
UltraSoC Technologies Ltd.
March 20, 2020
**************************************************************
..............................................................
*

Assumptions: 

1- Synchronization will be added later. 
This version assumes synch time is infinity: i.e. no synch is done for now. 
2- Interface signals implemented for now are: itype[3:0], cause[2:0]
#CHECK, tval[31:0], priv[1:0], iaddr[31:0], iretire[0:0]. 
3- Details of some signals: cause is composed of: ucause/scause/mcause, each one bit for now 
#CHECK, priv has 2 bits to express 4 levels for now: 
user(ABI), os(SBI), hypervisor(HBI), HEE (HAL). 
iaddr is the address of the first inst in a block, 
iretire Number of instructions retired in this block 1 or 0. 
4- Here only single retirement per bock is implemented


The above metnioned specs specifies the following: 


Instruction delta tracing

Summary of the specs:

2. Branches

2.1.1

- the instructions executed unconditionally 
or at least their execution can be determined based on the program binary;
do not need to be reported ib the trace. 

2.1.2
- for uninfereable program counter discontinuity like indirect jumps, 
the instruction delta trace must include a destination address: 
the address of the next valid instruction.

2.1.3
- the trace must include whether a branch was taken or not 
(RISC-v only supports direct branches where the dist is known, so no futher info is required)

2.1.4
- the trace must report the address where normal program flow ceased, 
- the trace must give an indication of the asynchronous destination by reporting for ex the exception type. 

- When an interrupt or exception occurs, 
the address of final instruction retired beforehand must be traced.
- Following this the next valid instruction address (the first of the trap handler) must be traced.

2.1.5
- Synchronization is accomplished by sending a full valued instruction address 
(and potentially a context identifier). The sending of the reason for synchronizing is optional.
- The frequency of synchronization is configurable, but it must happen as well in case: 
1) start, 
2) if any instruction tracing was missed, 
3) at the first inst of an interrupt service routine or exception handler. 
- when tracing stops for any reason, the address of the final traced instruction must be output.

2.2 Modes: Full address mode first , then we can think about implementing delta mode

3. Hart to encoder interface

3.1 
• The number of instructions that are being retired;
• Whether there has been an exception or interrupt, and if so 
      the cause (from the ucause/scause/mcause CSR) 
      and trap value (from the utval/stval/mtval CSR);
• The current privilege level of the RISC-V hart;
• The instruction_type of retired instructions for:
   – Jumps with a target that cannot be inferred from the source code;
   – Taken and nontaken branches;
   – Return from exception or interrupt (*ret instructions).
• The instruction_address for:
   – Jumps with a target that cannot be inferred from the source code;
   – The instruction retired immediately after a jump with a target that cannot be inferred
      from the source code (also referred to as the target or destination of the jump);
   – Taken and nontaken branches;
   – The last instruction retired before an exception or interrupt;
   – The first instruction retired following an exception or interrupt;
   – The last instruction retired before a privilege change;
   – The first instruction retired following a privilege change.

3.1.1
  optional: the jump instruction classification 
  (calls, tail-calls, returns, Co-routine swap, and otehr)
3.1.2 
  we consider only one hart
3.2 signals classification
Notice that this trace-specs diffrentiate between block and instruction retirements, 
  here we will implement only instruction retirement at first


---iaddr: the start of a contiguous block of instructions, all of which retired in the same cycle

---iretire: contains the number of half-words represented by instructions retired in a block
--> contradicts table 3.3 iretire[0:0] SR Number of instructions retired in this block (0 or 1).

---ilastsize: the size of the last instruction. 
     The size of the last retired instruction is 2^ilastsize half-words.

---itype: if itype is 1 or 2 (indicating an exception or an interrupt), 
the number of instructions retired may be zero
itype can be 3 or 4 bits wide. If itype_width_p is 3, 
a single code (6) is used to indicate all uninferable jumps.

0: Final instruction in the block is none of the other named itype codes
1: Exception. An exception that traps occurred following the final retired instruction in the block
2: Interrupt. An interrupt that traps occurred following the final retired instruction in the block
3: Exception or interrupt return
4: Nontaken branch
5: Taken branch
6: Uninferable jump if itype_width_p is 3, reserved otherwise
7: reserved
8: Uninferable call
9: Inferrable call
10: Uninferable tail-call
11: Inferrable tail-call
12: Co-routine swap
13: Return
14: Other uninferable jump
15: Other inferable jump

--------cause and tval are only defined if
itype is 1 or 2. If iretire=0 and itype=0, the values of all other signals are undefined

---cause[ecause_width_p-1:0] M Exception or interrupt cause (ucause/scause/mcause). 
Ignored unless itype=1 or 2
---tval[iaddress_width_p-1:0] M associated trap value, e.g. the faulting virtual address for 
address exceptions, as would be written to the utval/stval/mtval CSR
---priv[privilege_width_p-1:0] M Privilege level for all instructions retired on this cycle.

---ctype[ctype_width_p-1:0] O Reporting behavior for context:
	0: Don’t report;
	1: Report imprecisely;
	2: Report precisely;
	3: Report as asynchronous discontinuity.
We'll use only 0: don't report, as context[context_width_p-1:0] is not going to be implemented. 

---sijump: OR If itype indicates that this block ends with an uninferable discontinuity, 
setting this signal to 1 indicates that it is sequentially inferable and may be treated 
as inferable by the encoder if the
preceding auipc, lui or c.lui has been traced. Ignored for itype codes other than 8, 10, 12 or 14.
If the encoder offers an sijump input it must also provide a parameter to indicate 
whether the input is connected to a hart that implements this capability

4. Filtering is not going to be implemented

5. Packets: first version would just write data to file



modes: 
ibex does not have branch prediction, so all related modes are irrelevant. 
Here onlx delta and full address modes are going to be implemented. 

most of parameters in table 7.1 
are not implemented, the default value is assumed. 
If something from there is needed, it will be updated here.


Compressed instructions are not yet supported. 

We assume instructions are correct. 

*/


module ibex_rv_trace #(
  parameter logic [2:0]  mode // full address (000) or delta mode(001), 
                              // other bits for future modes
) (
  input logic         clk_i,
  input logic         rst_ni,

  // #REVIEW_REQ: remove this?
  input logic [31:0]  hart_id_i,


  // rv_trace_spec signals 
  input logic [1:0]   trace_ctype, // the type of reporting required by the tracer module, 
                            // for now still not reports are generated, 0: Don’t report
  output logic [3:0]  trace_itype, // takes values from 0 to 15 in page 18 in specs , 
                                   // we'll use now 6 for all uninferrable jumps 
                                   // as if 3 bits only are used
  output logic [31:0] trace_iaddr, // information presented in a block represents a contiguous 
                                   // block of instructions starting at iaddr
  output logic [11:0] trace_cause, // ucause/scause/mcause #REVIEW_REQ how many bits are needed?
  output logic [31:0] trace_tval, // trap address, relevant only when itype = 1 or 2
  output logic [1:0]  trace_priv, // takes value for each retired inst, here single inst retirement,
                            // then each retired, hence logged inst has associated priv with inst
  output logic [0:0]  trace_iretire, // one bit for single retirement per bock


  // signals inherited from ibex_tracer
  input logic        i_valid, // indication from external checker that the instruction is valid
  input logic [63:0] i_order,
  input logic [31:0] i_insn, // to be able to decode the type to deduce itype for jal, jalr
  input logic        i_trap, // no decode is needed if we can already know from i_trap 
  //input logic        i_halt, // #REVIEW_REQ: do we need this?
  input logic        i_intr, // no decode is needed if we can already know from i_intr

  input logic [31:0] i_pc_rdata,
  input logic [31:0] i_pc_wdata // #REVIEW_REQ: do we need this? 

//  #REVIEW_REQ: Do we need these signals? I guess no, but confirm. 
//  input logic [31:0] i_mem_addr,
//  input logic [ 3:0] i_mem_rmask,
//  input logic [ 3:0] i_mem_wmask,
//  input logic [31:0] i_mem_rdata,
//  input logic [31:0] i_mem_wdata,

/*
//Signals from el2 core, ignored here 
//from https://github.com/chipsalliance/Cores-SweRV-EL2/blob/master/design/el2_swerv.sv
#REVIEW_REQ: Confirm removing them
   output logic [31:0] trace_rv_i_insn_ip,
   output logic [31:0] trace_rv_i_address_ip,
   output logic [1:0]  trace_rv_i_valid_ip, // instr_valid_i
   output logic [1:0]  trace_rv_i_exception_ip, // exc_pc_mux_o   :  wb_exception? 
   output logic [4:0]  trace_rv_i_ecause_ip, // exc_cause_o
   output logic [1:0]  trace_rv_i_interrupt_ip, // csr_mstatus_mie_i
   output logic [31:0] trace_rv_i_tval_ip // csr_mtval_o
*/

);

//

  int unsigned cycle;

  logic inst_valid = i_valid; 
  logic trace_address = 0;
  logic s_inst_jal, s_inst_jalr = 0; 
  logic inst_ret = 0;
  logic s_inst_br = 0; // a signal indicating whether the instruction is branch or not
  logic br_nottaken = 1;
  logic br_taken = 1;

  logic dummy_i_pc_wdata = i_pc_wdata; // dummy signal for now or see #MARK1 below

//

  // cycle counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cycle <= 0;
    end else begin
      cycle <= cycle + 1;
    end
  end

//
// Check if the pc is return from interrupt of exception

//
// Check if uninterrable jump with jal or jalr

//
// Check if inst is branch, and then if it is taken or not, assign s_inst_br

//

  trace_itype = 000;

  if ( inst_valid ) begin
  // inst_valid
    trace_iretire = 1; 
    if ( i_trap ) begin // 1: Exception.
      trace_itype = 001;
    end
    if ( i_intr ) begin
      trace_itype = 010;  // 2: Interrupt.
    end
    if ( inst_ret ) begin
      trace_itype = 011;  // 3: Exception or interrupt return
    end
    if ( s_inst_br and br_nottaken ) begin
      trace_itype = 100;  // 4: Nontaken branch
    end
    if ( s_inst_br and br_taken ) begin
      trace_itype = 101;  // 5: Taken branch
    end
    if ( s_inst_jal or s_inst_jalr ) begin // 6: Uninferable jump if itype_width_p is 3, reserved otherwise
      trace_itype = 110;
    end
  // inst_valid
  end
  // #REVIEW_REQ: what should we do if the inst is not valid?

  if ( trace_itype != 0 ) begin
    trace_address = 1;
    trace_iaddr = i_pc_rdata ; 
  end

  if ( trace_address ) begin
    trace_tval = i_pc_wdata; //  #REVIEW_REQ: which pc should be input? or i_pc_rdata #MARK1
  end

//
  trace_cause = 000000000000; // Dummy value for now // #TODO analyse cause correctly and assign it
//
  trace_priv = 00; // usr app for now // #TODO add other priv later
//

endmodule
