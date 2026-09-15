open Sail_lib;;
module P = Platform_impl;;
module Elf = Elf_loader;;

(* Platform configuration *)

let config_enable_rvc                  = ref true
let config_enable_next                 = ref false
let config_enable_writable_misa        = ref true
let config_enable_dirty_update         = ref false
let config_enable_misaligned_access    = ref false
let config_mtval_has_illegal_inst_bits = ref false
let config_enable_writable_fiom        = ref true
let config_enable_vext                 = ref true
let config_pmp_count                   = ref Big_int.zero
let config_pmp_grain                   = ref Big_int.zero

let set_config_pmp_count x = config_pmp_count := Big_int.of_int x
let set_config_pmp_grain x = config_pmp_grain := Big_int.of_int x

let platform_arch = ref P.RV64

(* logging *)

let config_print_instr       = ref true
let config_print_reg         = ref true
let config_print_mem_access  = ref true
let config_print_platform    = ref true

let print_instr s =
  if !config_print_instr
  then print_endline s
  else ()

let print_reg s =
  if !config_print_reg
  then print_endline s
  else ()

let print_mem_access s =
  if !config_print_mem_access
  then print_endline s
  else ()

let print_platform s =
  if !config_print_platform
  then print_endline s
  else ()

let get_config_print_instr () = !config_print_instr
let get_config_print_reg () = !config_print_reg
let get_config_print_mem () = !config_print_mem_access
let get_config_print_platform () = !config_print_platform

(* Mapping to Sail externs *)
let cur_arch_bitwidth () =
  match !platform_arch with
    | P.RV64 -> Big_int.of_int 64
    | P.RV32 -> Big_int.of_int 32

let arch_bits_of_int i =
  get_slice_int (cur_arch_bitwidth (), Big_int.of_int i, Big_int.zero)

let arch_bits_of_int64 i =
  get_slice_int (cur_arch_bitwidth (), Big_int.of_int64 i, Big_int.zero)

let rom_size_ref = ref 0
let make_rom arch start_pc =
  let reset_vec =
    List.concat (List.map P.uint32_to_bytes (P.reset_vec_int arch start_pc)) in
  let dtb = P.make_dtb (P.make_dts arch) in
  let rom = reset_vec @ dtb in
  ( rom_size_ref := List.length rom;
    (*
    List.iteri (fun i c ->
                print_mem_access "rom[0x%Lx] <- %x\n"
                                 (Int64.add P.rom_base (Int64.of_int i))
                                 c
               ) rom;
     *)
    rom )

let enable_writable_misa ()          = !config_enable_writable_misa
let enable_rvc ()                    = !config_enable_rvc
let enable_next ()                   = !config_enable_next
let enable_fdext ()                  = false
let enable_vext ()                   = !config_enable_vext
let enable_dirty_update ()           = !config_enable_dirty_update
let enable_misaligned_access ()      = !config_enable_misaligned_access
let mtval_has_illegal_inst_bits ()   = !config_mtval_has_illegal_inst_bits
let enable_zfinx ()                  = false
let enable_writable_fiom ()          = !config_enable_writable_fiom
let pmp_count ()                     = !config_pmp_count
let pmp_grain ()                     = !config_pmp_grain

let rom_base ()   = arch_bits_of_int64 P.rom_base
let rom_size ()   = arch_bits_of_int   !rom_size_ref

let dram_base ()  = arch_bits_of_int64 P.dram_base
let dram_size ()  = arch_bits_of_int64 !P.dram_size_ref

let clint_base () = arch_bits_of_int64 P.clint_base
let clint_size () = arch_bits_of_int64 P.clint_size

let insns_per_tick () = Big_int.of_int P.insns_per_tick

let htif_tohost () =
  arch_bits_of_int64 (Big_int.to_int64 (Elf.elf_tohost ()))

(* Entropy Source - get random bits *)

(* This function can be changed to support deterministic sequences of
   pseudo-random bytes. This is useful for testing. *)
let get_16_random_bits () = arch_bits_of_int (Random.int 0xFFFF)

(* load reservation *)

let speculate_conditional () = true

let reservation = ref "none"  (* shouldn't match any valid address *)

let load_reservation addr =
  print_platform (Printf.sprintf "reservation <- %s\n" (string_of_bits addr));
  reservation := string_of_bits addr

let match_reservation addr =
  print_platform (Printf.sprintf "reservation: %s, key=%s\n" (!reservation) (string_of_bits addr));
  string_of_bits addr = !reservation

let cancel_reservation () =
  print_platform (Printf.sprintf "reservation <- none\n");
  reservation := "none"

let read_mem (rk, addrsize, addr, len) =
  Sail_lib.fast_read_ram (len, addr)

let write_mem_ea _ = ()

let write_mem (wk, addrsize, addr, len, value) =
  Sail_lib.write_ram' (len, Sail_lib.uint addr, value); true

let excl_res _ = true

let barrier _ = ()

(* terminal I/O *)

let term_write char_bits =
  let big_char = Big_int.bitwise_and (uint char_bits) (Big_int.of_int 255) in
  P.term_write (char_of_int (Big_int.to_int big_char))

let term_read () =
  let c = P.term_read () in
  arch_bits_of_int (int_of_char c)

(* physical memory *)

let get_mem_bytes addr len =
  read_mem_bytes addr len

(* returns starting value for PC, i.e. start of reset vector *)
let init arch elf_file =
  platform_arch := arch;
  Elf.load_elf elf_file;

  print_platform (Printf.sprintf "\nRegistered htif_tohost at 0x%Lx.\n" (Big_int.to_int64 (Elf.elf_tohost ())));
  print_platform (Printf.sprintf "Registered clint at 0x%Lx (size 0x%Lx).\n%!" P.clint_base P.clint_size);

  let start_pc = Elf.Big_int.to_int64 (Elf.elf_entry ()) in
  let rom = make_rom arch start_pc in
  let rom_base = Big_int.of_int64 P.rom_base in
  let rec write_rom ofs = function
    | [] -> ()
    | h :: tl -> let addr = Big_int.add rom_base (Big_int.of_int ofs) in
                 (wram addr h);
                 write_rom (ofs + 1) tl
  in ( write_rom 0 rom;
       get_slice_int (cur_arch_bitwidth (), rom_base, Big_int.zero)
     )
