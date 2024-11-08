

#include "svdpi.h"
/** it should have a dedicade header file */


#define STRINGIFY(x) #x
#define TOSTRING(x) STRINGIFY(x)

// Concatenate macros
#define CONCATENATE(a, b) a##b
#define CONCATENATE2(a, b) CONCATENATE(a, b)

#ifndef TOPLEVEL_NAME
#error "TOPLEVEL_NAME must be set to the name of the toplevel."
#else
#pragma message ("TOPLEVEL_NAME is set to: " TOSTRING(TOPLEVEL_NAME))
#endif

// Construct the include _Dpi.h file name
#define TOP_LEVEL_DPI_HEADER_NAME CONCATENATE2(V, TOPLEVEL_NAME)__Dpi.h

// Construct the include top module file name
#define TOP_LEVEL_HEADER_NAME CONCATENATE2(V, TOPLEVEL_NAME).h

#define TOP_LEVEL_DUT CONCATENATE2(V, TOPLEVEL_NAME)

//#include TOSTRING(TOP_LEVEL_DPI_HEADER_NAME)
#include TOSTRING(TOP_LEVEL_HEADER_NAME)


/**header file ends here */

#include "verilated_vcd_c.h"
#include "verilated.h"

#include <iostream>
#include <iomanip>
#include <fstream>
#include <exception>
#include <cstdio>
#include <cstdint>
#include <cerrno>

void dump_memory();
double sc_time_stamp();

static vluint64_t t = 0;
TOP_LEVEL_DUT *top;

int main(int argc, char **argv, char **env)
{
uint32_t timeOut{207374};
#ifdef MCY
    int mutidx = 0;
    for (int i = 1; i < argc; i++)
    {
      if (!strcmp(argv[i], "--mutidx") && i+1 < argc)
      {
        i++;
        std::string s(argv[i]);
        mutidx = std::stoi(s);
      }
    }
#endif

    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);
    top = new TOP_LEVEL_DUT();

    // svSetScope(svGetScopeFromName(
    //     "TOP.tb_top_verilator.cv32e40p_tb_wrapper_i.ram_i.dp_ram_i"));
    // Verilated::scopesDump();

#ifdef VCD_TRACE
    VerilatedVcdC *tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open("verilator_tb.vcd");
#endif
    top->fetch_enable_i = 1;
    top->clk_i          = 0;
    top->rst_ni         = 1;

    top->eval();
#ifdef DUMP_MEMORY    
    dump_memory();
#endif    

#ifdef MCY
    // svSetScope(svGetScopeFromName(
    //     "TOP.tb_top_verilator.cv32e40p_tb_wrapper_i.riscv_core_i.ex_stage_i.alu_i.int_div.div_i"));
    svLogicVecVal idx = {0};
    idx.aval = mutidx;
    set_mutidx(&idx);
    std::cout << "[tb_top_verilator] mutsel = " << idx.aval << "\n";
#endif

    while (!Verilated::gotFinish() && t < timeOut) {
        if(t<15)
            top->rst_ni = 0;
        if (t > 40)
            top->rst_ni = 1;
        top->clk_i = !top->clk_i;
        top->eval();
#ifdef VCD_TRACE
        tfp->dump(t);
#endif
        t += 5;
    }
#ifdef VCD_TRACE
    tfp->close();
#endif
    delete top;
    exit(0);
}

double sc_time_stamp()
{
    return t;
}

#ifdef DUMP_MEMORY  
void dump_memory()
{
    errno = 0;
    std::ofstream mem_file;
    svLogicVecVal addr = {0};

    mem_file.exceptions(std::ofstream::failbit | std::ofstream::badbit);
    try {
        mem_file.open("memory_dump.bin");
        for (size_t i = 0; i < 1048576; i++) {
            addr.aval    = i;
            uint32_t val = read_byte(&addr);
            //uint32_t val = read_byte(&addr.aval);  // mike@openhwgroup.org: if the above line fails to compile on your system, try this line
            mem_file << std::setfill('0') << std::setw(2) << std::hex << val
                     << std::endl;
        }
        mem_file.close();

        std::cout << "[tb_top_verilator] finished dumping memory" << std::endl;

    } catch (std::ofstream::failure e) {
        std::cerr << "[tb_top_verilator] exception opening/reading/closing file memory_dump.bin\n";
    }
}
#endif