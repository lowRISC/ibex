(* Simple trace comparison checker *)

type arch =
  | RV32
  | RV64

type csr_read = {
  csrr : string;
  rdval : int64
}

type csr_write = {
  csrw : string;
  wrval : int64
}

type reg_write = {
  reg : int;
  rval : int64
}

type mem_op = {
  vaddr : int64;
  paddr : int64;
  mval  : int64
}

type inst = {
  count : int;
  priv : char;
  pc : int64;
  inst: int32
}

type tick = {
  time : int64
}

type htif = {
  tohost : int64
}

type ld_res =
  | Res_make of int64
  | Res_match of int64 * int64
  | Res_cancel

type line =
  | L_none
  | L_inst of inst
  | L_reg_write of reg_write
  | L_csr_read of csr_read
  | L_csr_write of csr_write
  | L_mem_read of mem_op
  | L_mem_write of mem_op
  | L_tick of tick
  | L_htif of htif
  | L_ld_res of ld_res

(* architectural support *)
let sail_arch = ref RV64

let arch_val v =
  match !sail_arch with
    | RV64 -> v
    | RV32 -> Int64.logand v 0xFFFFFFFFL (* only lowest 32-bits *)

let inst_count = ref 0

(* csr reads
   CSR mscratch -> 0x0000000000000000
 *)

let parse_csr_read l =
  try Scanf.sscanf l " CSR %s -> 0x%Lx"
                   (fun csrr rdval -> L_csr_read { csrr; rdval = arch_val rdval })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_csr_read r =
  Printf.sprintf "CSR %s -> 0x%Lx" r.csrr r.rdval

(* csr writes
   CSR mstatus <- 0x0000000a00020800 (input: 0x0000000a00020800)
 *)

let parse_csr_write l =
  try Scanf.sscanf l " CSR %s <- 0x%Lx "
                   (fun csrw wrval -> L_csr_write { csrw; wrval = arch_val wrval })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_csr_write r =
  Printf.sprintf "CSR %s <- 0x%Lx " r.csrw r.wrval

(* mem reads
   mem[V:0x0000000080001000, P:0x0000000080001000] -> 0x0000000000000000
 *)

(* exclusion list, to avoid comparing reads to mmio htif port by spike *)
let mem_addr_excludes = [ 0x80001000L ]
let parse_mem_read l =
  try Scanf.sscanf l " mem[V:0x%Lx, P:0x%Lx] -> 0x%Lx"
                   (fun va pa v ->
                    if List.mem va mem_addr_excludes || List.mem pa mem_addr_excludes
                    then L_none
                    else L_mem_read { vaddr = arch_val va; paddr = arch_val pa; mval = arch_val v })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_mem_read r =
  Printf.sprintf "mem[V:0x%Lx, P:0x%Lx] -> 0x%Lx" r.vaddr r.paddr r.mval

(* mem writes
   mem[V:0x0000000080001000, P:0x0000000080001000] <- 0x0000000000000000
 *)

let parse_mem_write l =
  try Scanf.sscanf l  " mem[V:0x%Lx, P:0x%Lx] <- 0x%Lx"
                   (fun va pa v ->
                    L_mem_write { vaddr = arch_val va; paddr = arch_val pa; mval = arch_val v })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_mem_write r =
  Printf.sprintf "mem[V:0x%Lx, P:0x%Lx] -> 0x%Lx" r.vaddr r.paddr r.mval

(* reg writes
   x16 <- 0x0000000000000000
 *)

let parse_reg_write l =
  try Scanf.sscanf l " x%u <- 0x%Lx"
                  (fun reg rval -> L_reg_write { reg; rval = arch_val rval })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_reg_write r =
  Printf.sprintf "x%u <- 0x%Lx" r.reg r.rval

(* instructions *)

let sprint_inst r =
  Printf.sprintf "[%u] [%c]: 0x%Lx (0x%lx)" r.count r.priv r.pc r.inst

(* sail instruction line:
  [13000] [M]: 0x0000000080000E4A (0x0107971B) slli  a4, a5, 0b10000
 *)

let parse_sail_inst l =
  try Scanf.sscanf l " [%u] [%c]: 0x%Lx (0x%lx) %s"
                   (fun count  priv  pc inst _ ->
                    inst_count := count;
                    L_inst { count; priv; pc; inst })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

(* spike instruction line:
  [2] core   0 [M]: 0x0000000000001008 (0xf1402573) csrr    a0, mhartid
 *)

let parse_spike_inst l =
  try Scanf.sscanf l " [%u] core   0 [%c]: 0x%Lx (0x%lx) %s"
                   (fun count  priv  pc inst _ ->
                    inst_count := count;
                    L_inst { count; priv; pc = arch_val pc; inst })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

(* clock tick
   clint::tick mtime <- 0x1
 *)

let parse_tick l =
  try Scanf.sscanf l " clint::tick mtime <- 0x%Lx"
                   (fun time -> L_tick { time })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_tick t =
  Printf.sprintf "clint::tick mtime <- 0x%Lx" t.time

(* htif tick
   htif::tick 0x1
 *)

let parse_htif l =
  try Scanf.sscanf l " htif::tick 0x%Lx"
                   (fun tohost -> L_htif { tohost })
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_htif t =
  Printf.sprintf "htif::tick 0x%Lx" t.tohost

(* Load reservations:
   make:   reservation <- 0x80002008
   match:  reservation: 0xffffffffffffffff, key=0x80002008
   cancel: reservation <- none

 *)
let parse_ldres_match l =
  try Scanf.sscanf
        l " reservation: 0x%Lx, key=0x%Lx"
                   (fun res key -> L_ld_res (Res_match (res, key)))
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let parse_ldres_match_sail l =
  try Scanf.sscanf
        l " reservation: none, key=0x%Lx"
                   (fun key -> L_ld_res (Res_match (Int64.minus_one, key)))
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let parse_ldres_change l =
  try if l = "reservation <- none"
      then L_ld_res Res_cancel
      else Scanf.sscanf
             l " reservation <- 0x%Lx"
             (fun res -> L_ld_res (Res_make res))
  with
    | Scanf.Scan_failure _ -> L_none
    | End_of_file -> L_none

let sprint_ldres = function
  | Res_make res         -> Printf.sprintf "reservation <- 0x%Lx" res
  | Res_match (res, key) -> Printf.sprintf "reservation: 0x%Lx, key=0x%Lx" res key
  | Res_cancel           -> Printf.sprintf "reservation <- none"

(* scanners *)

let popt p l = function
  | L_none -> p l
  | res -> res

let parse_line l =
  parse_csr_read l |> popt parse_csr_write l
  |> popt parse_reg_write l |> popt parse_tick l |> popt parse_htif l
  |> popt parse_ldres_change l  |> popt parse_ldres_match l

let parse_sail_line l =
  parse_line l |> popt parse_sail_inst l  |> popt parse_ldres_match_sail l

let parse_spike_line l =
  parse_line l |> popt parse_spike_inst l

(* printer *)
let sprint_line = function
  | L_none -> "<not-parsed>"
  | L_inst i -> sprint_inst i
  | L_reg_write r -> Printf.sprintf "<%d> %s" !inst_count (sprint_reg_write r)
  | L_csr_read  r -> Printf.sprintf "<%d> %s" !inst_count (sprint_csr_read r)
  | L_csr_write r -> Printf.sprintf "<%d> %s" !inst_count (sprint_csr_write r)
  | L_mem_read  m -> Printf.sprintf "<%d> %s" !inst_count (sprint_mem_read m)
  | L_mem_write m -> Printf.sprintf "<%d> %s" !inst_count (sprint_mem_write m)
  | L_tick t      -> Printf.sprintf "<%d> %s" !inst_count (sprint_tick t)
  | L_htif t      -> Printf.sprintf "<%d> %s" !inst_count (sprint_htif t)
  | L_ld_res r    -> Printf.sprintf "<%d> %s" !inst_count (sprint_ldres r)

(* file processing *)

let rec get_line ch parse =
  let line = try  Some (input_line ch)
             with End_of_file -> None in
  match line with
    | Some l -> (match parse l with
                   | L_none -> get_line ch parse
                   | r -> r
                )
    | None -> L_none

let rec print_lines ch parse =
  match (get_line ch parse) with
    | L_none -> ()
    | l      -> (print_endline (sprint_line l);
                 print_lines ch parse)


let lines_matched k l =
  match k, l with
    (* Special case for CSR writes to sie/sip/sstatus, since spike
     * does a recursive call which messes the trace log.  For these
     * registers, we just match the final written value, and need to
     * unfortunately ignore the input value.
     *)
    | L_csr_write kw, L_csr_write lw ->
          if   (   (kw.csrw = "mie"     && lw.csrw = "sie")
                || (kw.csrw = "mip"     && lw.csrw = "sip")
                || (kw.csrw = "mstatus" && lw.csrw = "sstatus"))
          then kw.wrval = lw.wrval
          else kw = lw
    | _, _ ->   k = l

let rec compare_traces k l cnt =
  let kro = get_line k parse_spike_line in
  let lro = get_line l parse_sail_line in
  match kro, lro with
    | L_none, L_none ->
          print_endline (Printf.sprintf "Matched %d instructions" cnt)
    | L_none, lr ->
          print_endline  "Spike: not reached";
          print_endline ("Sail:  " ^ sprint_line lr);
          exit 1
    | kr, L_none ->
          print_endline ("Spike: " ^ sprint_line kr);
          print_endline  "Sail:  not reached";
          exit 1
    | kr, lr ->
          if   lines_matched kr lr
          then compare_traces k l (cnt + 1)
          else (print_endline ("Spike: " ^ sprint_line kr);
                print_endline ("Sail:  " ^ sprint_line lr);
                exit 1)

let spike_log  = ref (None : string option)
let sail_log   = ref (None : string option)
let uncompress = ref false

let in_file f =
  if !uncompress
  then Unix.open_process_in ("gunzip -c " ^ f)
  else open_in f

let options =
  Arg.align ([( "-z",
                Arg.Set uncompress,
                " uncompress trace files");
              ( "-rv32",
                Arg.Unit (fun f -> sail_arch := RV32),
                " sail architecture");
              ( "-k",
                Arg.String (fun f -> spike_log := Some f),
                " spike trace log");
              ( "-l",
                Arg.String (fun f -> sail_log := Some f),
                " sail trace log")])
let usage = "usage: tracecmp [options]\n"

let _ =
  Arg.parse options (fun s -> print_endline usage; exit 0)
            usage;
  match !spike_log, !sail_log with
    | None, None     -> (print_endline usage; exit 0)
    | Some l, None   -> print_lines (in_file l) parse_spike_line
    | None, Some l   -> print_lines (in_file l) parse_sail_line
    | Some k, Some l -> compare_traces (in_file k) (in_file l) 0
