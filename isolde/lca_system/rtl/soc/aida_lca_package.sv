// Copyleft ISOLDE 2025

package aida_lca_package;
  import isolde_tcdm_pkg::*;
  //
  /* see bsp/link.ld
MEMORY
{
    instrram    : ORIGIN = 0x00100000, LENGTH = 0x8000
    dataram     : ORIGIN = 0x00110000, LENGTH = 0x30000
    stack       : ORIGIN = 0x00140000, LENGTH = 0x30000
}
*/
  localparam rule_addr_t IMEM_ADDR = 32'h00100000;
  localparam int unsigned IMEM_SIZE = 32'h08000;
  localparam rule_addr_t DMEM_ADDR = 32'h00110000;
  localparam int unsigned DMEM_SIZE = 32'h30000;
  localparam rule_addr_t SMEM_ADDR = 32'h00140000;
  localparam int unsigned SMEM_SIZE = 32'h30000;
  localparam int unsigned GMEM_SIZE = SMEM_ADDR + SMEM_SIZE - IMEM_ADDR;
  //  see reset vector in bsp/crt0.S
  localparam rule_addr_t BOOT_ADDR = 32'h00100080;
  localparam rule_addr_t PERIPH_ADDR = 32'h00001000;
  //see bsp/simple_system_regs.h
  localparam rule_addr_t MMIO_ADDR = 32'h8000_0000;
  localparam rule_addr_t MMIO_ADDR_END = 32'h8000_0080;

  // === debugger module parameters ===
  localparam rule_addr_t DEBUG_ADDR = 32'h1A11_0000;
  localparam int unsigned DEBUG_SIZE = 32'h0000_1000;
  // === spm narrow port start ====
  localparam rule_addr_t SPM_NARROW_ADDR = 32'h8000_1000;
  localparam int unsigned SPM_NARROW_SIZE = 32'h0000_1000;  //4kB

  // === hardware accelerator parameters ===
  localparam int unsigned NC = 1;
  localparam int unsigned HCI_AW = redmule_pkg::ADDR_W;
  localparam int unsigned HCI_DW = redmule_pkg::DATA_W;
  localparam int unsigned MP = HCI_DW / 32;
  localparam int unsigned N_TCDM_BANKS = HCI_DW / 32;
  localparam logic REDMULE_TEST_MODE = 1'b0;  // set to 1 to enable test mode
endpackage  // aida_lca_package
