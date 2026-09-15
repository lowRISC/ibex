open Sail_lib
open Riscv
module PI = Platform_impl
module P = Platform
module Elf = Elf_loader

(* OCaml driver for generated RISC-V model. *)

let opt_file_arguments = ref ([] : string list)

let opt_dump_dts = ref false
let opt_dump_dtb = ref false
let opt_signature_file = ref (None : string option)
let signature_granularity_ref = ref 4
let opt_isa = ref (None : string option)

let report_arch () =
  Printf.printf "RV%d\n" (Big_int.to_int Riscv.zxlen_val);
  exit 0

let set_signature_file s =
  opt_signature_file := Some s;
  (* turn off logging *)
  P.config_print_instr := false;
  P.config_print_reg := false;
  P.config_print_mem_access := false;
  P.config_print_platform := false

let set_signature_granularity sg =
  signature_granularity_ref := sg

let options = Arg.align ([("-dump-dts",
                           Arg.Set opt_dump_dts,
                           " dump the platform device-tree source to stdout");
                          ("-dump-dtb",
                           Arg.Set opt_dump_dtb,
                           " dump the *binary* platform device-tree blob to stdout");
                          ("-enable-dirty-update",
                           Arg.Set P.config_enable_dirty_update,
                           " enable dirty-bit update during page-table walks");
                          ("-enable-misaligned-access",
                           Arg.Set P.config_enable_misaligned_access,
                           " enable misaligned accesses without M-mode traps");
                          ("-pmp-count",
                           Arg.Int P.set_config_pmp_count,
                           " number of supported PMPs (0, 16, 64)");
                          ("-pmp-grain",
                           Arg.Int P.set_config_pmp_grain,
                           " exponent of granularity of PMP addresses (G in the spec)");
                          ("-enable-next",
                           Arg.Set P.config_enable_next,
                           " enable N extension");
                          ("-mtval-has-illegal-inst-bits",
                           Arg.Set P.config_mtval_has_illegal_inst_bits,
                           " mtval stores instruction bits on an illegal instruction exception");
                          ("-enable-writable-fiom",
                           Arg.Set P.config_enable_writable_fiom,
                           " enable FIOM (Fence of I/O implies Memory) bit in menvcfg");
                          ("-disable-rvc",
                           Arg.Clear P.config_enable_rvc,
                           " disable the RVC extension on boot");
                          ("-disable-vext",
                           Arg.Clear P.config_enable_vext,
                           " disable the RVV extension on boot");
                          ("-disable-writable-misa-c",
                           Arg.Clear P.config_enable_writable_misa,
                           " leave misa hardwired to its initial value");
                          ("-ram-size",
                           Arg.Int PI.set_dram_size,
                           " size of physical ram memory to use (in MB)");
                          ("-report-arch",
                           Arg.Unit report_arch,
                           " report model architecture (RV32 or RV64)");
                          ("-test-signature",
                           Arg.String set_signature_file,
                           " file for signature output (requires ELF signature symbols)");
                          ("-signature-granularity",
                           Arg.Int set_signature_granularity,
                           " test signature granularity (in bytes)");
                          ("-isa",
                           Arg.String (fun s -> opt_isa := Some s),
                           " requested isa");
                          ("-with-dtc",
                           Arg.String PI.set_dtc,
                           " full path to dtc to use")
                         ])

let usage_msg = "RISC-V platform options:"

(* ELF architecture checks *)

let get_arch () =
  match Big_int.to_int Riscv.zxlen_val with
    | 64 -> PI.RV64
    | 32 -> PI.RV32
    | n  -> failwith (Printf.sprintf "Unknown model architecture RV%d" n)

let str_of_elf = function
  | Elf.ELF_Class_64 -> "ELF64"
  | Elf.ELF_Class_32 -> "ELF32"

let elf_arg =
  Arg.parse options (fun s -> opt_file_arguments := !opt_file_arguments @ [s])
            usage_msg;
  if !opt_dump_dts then (PI.dump_dts (get_arch ()); exit 0);
  if !opt_dump_dtb then (PI.dump_dtb (get_arch ()); exit 0);
  ( match !opt_file_arguments with
      | f :: _ -> prerr_endline ("Sail/RISC-V: running ELF file " ^ f); f
      | _ -> (prerr_endline "Please provide an ELF file."; exit 0)
  )

let check_elf () =
  match (get_arch (), Elf.elf_class ()) with
    | (PI.RV64, Elf.ELF_Class_64) ->
          P.print_platform "RV64 model loaded ELF64.\n"
    | (PI.RV32, Elf.ELF_Class_32) ->
          P.print_platform "RV32 model loaded ELF32.\n"
    | (a,  e) ->
          (let msg = Printf.sprintf "\n%s model cannot execute %s.\n" (PI.str_of_arch a) (str_of_elf e) in
           Printf.eprintf "%s" msg;
           exit 1)

(* post execution handlers *)

let write_bytes fl bytes =
  let i = ref 0 in
  while !i < Bytes.length bytes do
    for j = !signature_granularity_ref - 1 downto 0 do
      let s = Printf.sprintf "%02x"
          (int_of_char (Bytes.get bytes (!i + j))) in
      output_string fl s;
    done;
    output_string fl "\n";
    i := !i + !signature_granularity_ref;
  done

let write_signature f sig_start sig_end =
  let b = Big_int.to_int sig_start in
  let len = Big_int.to_int sig_end - b in
  let sig_bytes = P.get_mem_bytes sig_start len in
  let sig_file = open_out f in
  write_bytes sig_file sig_bytes;
  close_out sig_file

let dump_signature () =
  match !opt_signature_file with
  | None -> ()
  | Some f ->
      match (Elf.elf_symbol "begin_signature",
	     Elf.elf_symbol "end_signature") with
      | Some b, Some e -> write_signature f b e
      | None, _ -> Printf.eprintf "no begin_signature symbol in ELF"
      | _, None -> Printf.eprintf "no end_signature symbol in ELF"

let show_times init_s init_e run_e insts =
  let init_time = init_e.Unix.tms_utime -. init_s.Unix.tms_utime in
  let exec_time = run_e.Unix.tms_utime -. init_e.Unix.tms_utime in
  Printf.eprintf "\nInitialization: %g secs\n" init_time;
  Printf.eprintf "Execution: %g secs\n" exec_time;
  Printf.eprintf "Instructions retired: %Ld\n" insts;
  Printf.eprintf "Perf: %g ips\n" ((Int64.to_float insts) /. exec_time)

(* model execution *)

let run pc =
  sail_call
    (fun r ->
      try ( zinit_model ();
            zPC := pc;
            zloop ()
          )
      with
        | ZError_not_implemented (zs) ->
              print_string ("Error: Not implemented: ", zs)
        | ZError_internal_error (_) ->
              prerr_endline "Error: internal error"
    )

let () =
  Random.self_init ();

  let init_start = Unix.times () in
  let pc = Platform.init (get_arch ()) elf_arg in
  let _  = check_elf () in
  let init_end = Unix.times () in
  let _ = run pc in
  let run_end = Unix.times () in
  let insts = Big_int.to_int64 (uint (!Riscv.zminstret)) in
  dump_signature ();
  show_times init_start init_end run_end insts
