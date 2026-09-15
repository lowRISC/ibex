`ifndef SAIL_LIBRARY
`define SAIL_LIBRARY

// The Sail unit type.
typedef enum logic [0:0] {SAIL_UNIT=0} sail_unit;

// The Sail zero-width bitvector.
typedef enum logic [0:0] {SAIL_ZWBV=0} sail_zwbv;

`ifdef SAIL_NOSTRINGS

function automatic sail_unit sail_print_endline(sail_unit s);
   return SAIL_UNIT;
endfunction // sail_print_endline

function automatic sail_unit sail_prerr_endline(sail_unit s);
   return SAIL_UNIT;
endfunction // sail_prerr_endline

function automatic sail_unit sail_print(sail_unit s);
   return SAIL_UNIT;
endfunction // sail_print

function automatic sail_unit sail_prerr(sail_unit s);
   return SAIL_UNIT;
endfunction // sail_prerr

function automatic sail_unit sail_assert(bit b, sail_unit msg);
   return SAIL_UNIT;
endfunction // sail_assert

function automatic bit sail_eq_string(sail_unit s1, sail_unit s2);
   return 0;
endfunction

`else

function automatic sail_unit sail_print_endline(string s);
   $display(s);
   return SAIL_UNIT;
endfunction // sail_print_endline

function automatic sail_unit sail_prerr_endline(string s);
   $display(s);
   return SAIL_UNIT;
endfunction // sail_prerr_endline

function automatic sail_unit sail_print(string s);
   $write(s);
   return SAIL_UNIT;
endfunction // sail_print

function automatic sail_unit sail_prerr(string s);
   $write(s);
   return SAIL_UNIT;
endfunction // sail_prerr

function automatic sail_unit sail_assert(bit b, string msg);
   if (!b) begin
      $display("%s", msg);
   end;
   return SAIL_UNIT;
endfunction // sail_assert

function automatic bit sail_eq_string(string s1, string s2);
   return s1 == s2;
endfunction

`endif

typedef enum logic [0:0] {SAIL_REAL} sail_real;

`endif //  `ifndef SAIL_LIBRARY
