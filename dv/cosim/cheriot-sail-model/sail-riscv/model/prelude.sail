/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

default Order dec

$include <smt.sail>
$include <option.sail>
$include <arith.sail>
$include <string.sail>
$include "mapping.sail"
$include <vector_dec.sail>
$include <regfp.sail>
$include <generic_equality.sail>
$include "hex_bits.sail"


val not_bit : bit -> bit
function not_bit(b) = if b == bitone then bitzero else bitone

overload ~ = {not_bool, not_vec, not_bit}

// not_bool alias.
val not : forall ('p : Bool). bool('p) -> bool(not('p))
function not(b) = not_bool(b)

overload operator & = {and_vec}

overload operator | = {or_vec}

function bit_str(b: bit) -> string =
  match b {
    bitzero => "0b0",
    bitone => "0b1"
  }

overload BitStr = {bits_str, bit_str}

val int_power = {ocaml: "int_power", interpreter: "int_power", lem: "pow", coq: "pow", c: "pow_int"} : (int, int) -> int

overload operator ^ = {xor_vec, int_power, concat_str}

val sub_vec = {c: "sub_bits", _: "sub_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val sub_vec_int = {c: "sub_bits_int", _: "sub_vec_int"} : forall 'n. (bits('n), int) -> bits('n)

overload operator - = {sub_vec, sub_vec_int}

val quot_round_zero = {ocaml: "quot_round_zero", interpreter: "quot_round_zero", lem: "hardware_quot", c: "tdiv_int", coq: "Z.quot"} : (int, int) -> int
val rem_round_zero = {ocaml: "rem_round_zero", interpreter: "rem_round_zero", lem: "hardware_mod", c: "tmod_int", coq: "Z.rem"} : (int, int) -> int

/* The following defines % as euclidean modulus */
overload operator % = {emod_int}

val min_int = {ocaml: "min_int", interpreter: "min_int", lem: "min", coq: "min_atom", c: "min_int"} : forall 'x 'y.
  (int('x), int('y)) -> {'z, ('x <= 'y & 'z == 'x) | ('x > 'y & 'z == 'y). int('z)}

val max_int = {ocaml: "max_int", interpreter: "max_int", lem: "max", coq: "max_atom", c: "max_int"} : forall 'x 'y.
  (int('x), int('y)) -> {'z, ('x >= 'y & 'z == 'x) | ('x < 'y & 'z == 'y). int('z)}

overload min = {min_int}

overload max = {max_int}

val pow2 = "pow2" : forall 'n. atom('n) -> atom(2 ^ 'n)

val print = "print_endline" : string -> unit
val print_string = "print_string" : (string, string) -> unit

val print_instr    = {ocaml: "Platform.print_instr", interpreter: "print_endline", c: "print_instr", lem: "print_dbg", _: "print_endline"} : string -> unit
val print_reg      = {ocaml: "Platform.print_reg", interpreter: "print_endline", c: "print_reg", lem: "print_dbg", _: "print_endline"} : string -> unit
val print_mem      = {ocaml: "Platform.print_mem_access", interpreter: "print_endline", c: "print_mem_access", lem: "print_dbg", _: "print_endline"} : string -> unit
val print_platform = {ocaml: "Platform.print_platform", interpreter: "print_endline", c: "print_platform", lem: "print_dbg", _: "print_endline"} : string -> unit

val get_config_print_instr = {ocaml: "Platform.get_config_print_instr", c:"get_config_print_instr"} : unit -> bool
val get_config_print_reg = {ocaml: "Platform.get_config_print_reg", c:"get_config_print_reg"} : unit -> bool
val get_config_print_mem = {ocaml: "Platform.get_config_print_mem", c:"get_config_print_mem"} : unit -> bool
val get_config_print_exception = {ocaml: "Platform.get_config_print_exception", c:"get_config_print_exception"} : unit -> bool

val get_config_print_platform = {ocaml: "Platform.get_config_print_platform", c:"get_config_print_platform"} : unit -> bool
// defaults for other backends
function get_config_print_instr () = false
function get_config_print_reg () = false
function get_config_print_mem () = false
function get_config_print_platform () = false
function get_config_print_exception () = false

val sign_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
val zero_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)

function sign_extend(m, v) = sail_sign_extend(v, m)
function zero_extend(m, v) = sail_zero_extend(v, m)

val zeros_implicit : forall 'n, 'n >= 0 . implicit('n) -> bits('n)
function zeros_implicit (n) = sail_zeros(n)
overload zeros = {zeros_implicit}

val ones : forall 'n, 'n >= 0 . implicit('n) -> bits('n)
function ones (n) = sail_ones (n)

val bool_to_bit : bool -> bit
function bool_to_bit x = if x then bitone else bitzero

val bool_to_bits : bool -> bits(1)
function bool_to_bits x = [bool_to_bit(x)]

val bit_to_bool : bit -> bool
function bit_to_bool b = match b {
  bitone  => true,
  bitzero => false
}

val to_bits : forall 'l, 'l >= 0.(atom('l), int) -> bits('l)
function to_bits (l, n) = get_slice_int(l, n, 0)

infix 4 <_s
infix 4 >=_s
infix 4 <_u
infix 4 >=_u
infix 4 <=_u

val operator <_s  : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator >=_s : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator <_u  : forall 'n. (bits('n), bits('n)) -> bool
val operator >=_u : forall 'n. (bits('n), bits('n)) -> bool
val operator <=_u : forall 'n. (bits('n), bits('n)) -> bool

function operator <_s  (x, y) = signed(x) < signed(y)
function operator >=_s (x, y) = signed(x) >= signed(y)
function operator <_u  (x, y) = unsigned(x) < unsigned(y)
function operator >=_u (x, y) = unsigned(x) >= unsigned(y)
function operator <=_u (x, y) = unsigned(x) <= unsigned(y)

infix 7 >>
infix 7 <<

val "shift_bits_right" : forall 'n 'm. (bits('n), bits('m)) -> bits('n)
val "shift_bits_left"  : forall 'n 'm. (bits('n), bits('m)) -> bits('n)

val "shiftl" : forall 'm 'n, 'n >= 0. (bits('m), atom('n)) -> bits('m)
val "shiftr" : forall 'm 'n, 'n >= 0. (bits('m), atom('n)) -> bits('m)

overload operator >> = {shift_bits_right, shiftr}
overload operator << = {shift_bits_left, shiftl}

/* Ideally these would be sail builtin */

function shift_right_arith64 (v : bits(64), shift : bits(6)) -> bits(64) =
    let v128 : bits(128) = sign_extend(v) in
    (v128 >> shift)[63..0]

function shift_right_arith32 (v : bits(32), shift : bits(5)) -> bits(32) =
    let v64 : bits(64) = sign_extend(v) in
    (v64 >> shift)[31..0]

infix 7 >>>
infix 7 <<<

val rotate_bits_right : forall 'n 'm, 'm >= 0. (bits('n), bits('m)) -> bits('n)
function rotate_bits_right (v, n) =
    (v >> n) | (v << (to_bits(length(n), length(v)) - n))

val rotate_bits_left : forall 'n 'm, 'm >= 0. (bits('n), bits('m)) -> bits('n)
function rotate_bits_left (v, n) =
    (v << n) | (v >> (to_bits(length(n), length(v)) - n))

val rotater : forall 'm 'n, 'm >= 'n >= 0. (bits('m), atom('n)) -> bits('m)
function rotater (v, n) =
    (v >> n) | (v << (length(v) - n))

val rotatel : forall 'm 'n, 'm >= 'n >= 0. (bits('m), atom('n)) -> bits('m)
function rotatel (v, n) =
    (v << n) | (v >> (length(v) - n))

overload operator >>> = {rotate_bits_right, rotater}
overload operator <<< = {rotate_bits_left, rotatel}

function reverse_bits_in_byte (xs : bits(8)) -> bits(8) = {
  ys : bits(8) = zeros();
  foreach (i from 0 to 7)
    ys[i] = xs[7-i];
  ys
}

overload reverse = {reverse_bits_in_byte}

overload operator / = {quot_round_zero}
overload operator * = {mult_atom, mult_int}

/* helper for vector extension
 * 1. EEW between 8 and 64
 * 2. EMUL in vmv<nr>r.v instructions between 1 and 8
 */
val log2 : forall 'n, 'n in {1, 2, 4, 8, 16, 32, 64}. int('n) -> int
function log2(n) = {
  let result : int = match n {
    1    => 0,
    2    => 1,
    4    => 2,
    8    => 3,
    16   => 4,
    32   => 5,
    64   => 6
  };
  result
}
