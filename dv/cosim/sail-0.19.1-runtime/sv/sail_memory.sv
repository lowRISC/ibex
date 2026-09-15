`ifndef SAIL_MEMORY
`define SAIL_MEMORY

logic [7:0] sail_memory [logic [63:0]];

bit sail_tag_memory [logic [63:0]];

function automatic sail_bits sail_emulator_read_mem(logic [63:0] addrsize, sail_bits addr, sail_int n);
   logic [63:0] paddr;
   logic [SAIL_BITS_WIDTH-1:0] buffer;
   sail_int i;

   paddr = addr.bits[63:0];

   for (i = n; i > 0; i = i - 1) begin
      buffer = buffer << 8;
      buffer[7:0] = sail_memory[paddr + (i[63:0] - 1)];
   end

   return '{n[SAIL_INDEX_WIDTH-1:0] * 8, buffer};
endfunction

function automatic sail_bits sail_emulator_read_mem_ifetch(logic [63:0] addrsize, sail_bits addr, sail_int n);
   return sail_emulator_read_mem(addrsize, addr, n);
endfunction

function automatic sail_bits sail_emulator_read_mem_exclusive(logic [63:0] addrsize, sail_bits addr, sail_int n);
   return sail_emulator_read_mem(addrsize, addr, n);
endfunction

function automatic bit sail_emulator_write_mem(logic [63:0] addrsize, sail_bits addr, sail_int n, sail_bits value);
   logic [63:0] paddr;
   logic [SAIL_BITS_WIDTH-1:0] buffer;
   sail_int i;

   paddr = addr.bits[63:0];
   buffer = value.bits;

   for (i = 0; i < n; i = i + 1) begin
      sail_memory[paddr + i[63:0]] = buffer[7:0];
      buffer = buffer >> 8;
   end

   return 1'b1;
endfunction

function automatic bit sail_emulator_write_mem_exclusive(logic [63:0] addrsize, sail_bits addr, sail_int n, sail_bits value);
   return sail_emulator_write_mem(addrsize, addr, n, value);
endfunction

function automatic bit sail_emulator_read_tag(logic [63:0] addrsize, sail_bits addr);
   logic [63:0] paddr;
   paddr = addr.bits[63:0];
   if (sail_tag_memory.exists(paddr) == 1)
     return sail_tag_memory[paddr];
   else
     return 1'b0;
endfunction

function automatic sail_unit sail_emulator_write_tag(logic [63:0] addrsize, sail_bits addr, bit tag);
   logic [63:0] paddr;
   paddr = addr.bits[63:0];
   sail_tag_memory[paddr] = tag;
   return SAIL_UNIT;
endfunction

`endif
