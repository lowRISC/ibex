/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

function try_execute (x : ast) -> Retired = {
  try {
    execute(x)
  } catch {
    Error_not_rv32e_register() => { handle_illegal(); RETIRE_FAIL },
    e => throw e /* Rethrow other execptions */
  }
}

/* The emulator fetch-execute-interrupt dispatch loop. */

/* returns whether to increment the step count in the trace */
function step(step_no : int) -> bool = {
  /* for step extensions */
  ext_pre_step_hook();

  /*
   * This records whether or not minstret should be incremented when
   * the instruction is retired. Since retirement occurs before CSR
   * writes we initialise it based on mcountinhibit here, before it is
   * potentially changed. This is also set to false if minstret is
   * written.  See the note near the minstret declaration for more
   * information.
   */
  minstret_increment = mcountinhibit[IR] == 0b0;

  let (retired, stepped) : (Retired, bool) =
    match dispatchInterrupt(cur_privilege) {
      Some(intr, priv) => {
        if get_config_print_instr() | get_config_print_exception()
        then print("Handling interrupt PC=" ^ BitStr(PC) ^ " IRQ=" ^ BitStr(interruptType_to_bits(intr)));
        handle_interrupt(intr, priv);
        (RETIRE_FAIL, false)
      },
      None() => {
        /* the extension hook interposes on the fetch result */
        let f : FetchResult = ext_fetch_hook(fetch());
        match f {
          /* extension error */
          F_Ext_Error(e)   => {
            ext_handle_fetch_check_error(e);
            (RETIRE_FAIL, false)
          },
          /* standard error */
          F_Error(e, addr) => {
            handle_mem_exception(addr, e);
            (RETIRE_FAIL, false)
          },
          /* non-error cases: */
          F_RVC(h) => {
            instbits = zero_extend(h);
            let ast = ext_decode_compressed(h);
            if   get_config_print_instr()
            then {
              print_instr("[" ^ dec_str(step_no) ^ "] [" ^ to_str(cur_privilege) ^ "]: " ^ BitStr(PC) ^ " (" ^ BitStr(h) ^ ") " ^ to_str(ast));
            };
            /* check for RVC once here instead of every RVC execute clause. */
            if haveRVC() then {
              nextPC = PC + 2;
              (try_execute(ast), true)
             } else {
              handle_illegal();
              (RETIRE_FAIL, true)
             }
          },
          F_Base(w) => {
            instbits = zero_extend(w);
            let ast = ext_decode(w);
            if   get_config_print_instr()
            then {
              print_instr("[" ^ dec_str(step_no) ^ "] [" ^ to_str(cur_privilege) ^ "]: " ^ BitStr(PC) ^ " (" ^ BitStr(w) ^ ") " ^ to_str(ast));
            };
            nextPC = PC + 4;
            (try_execute(ast), true)
          }
        }
      }
    };

  tick_pc();

  /* update minstret */
  match retired {
    RETIRE_SUCCESS => retire_instruction(),
    RETIRE_FAIL    => ()
  };

  /* for step extensions */
  ext_post_step_hook();

  stepped
}

function loop () : unit -> unit = {
  let insns_per_tick = plat_insns_per_tick();
  i : int = 0;
  step_no : int = 0;
  while not(htif_done) do {
    let stepped = step(step_no);
    if stepped then step_no = step_no + 1;

    /* check htif exit */
    if htif_done then {
      let exit_val = unsigned(htif_exit_code);
      if exit_val == 0 then print("SUCCESS")
      else print_int("FAILURE: ", exit_val);
    } else {
      /* update time */
      i = i + 1;
      if i == insns_per_tick then {
        tick_clock();
        /* for now, we drive the platform i/o at every clock tick. */
        tick_platform();
        i = 0;
      }
    }
  }
}

/* initialize model state */
function init_model () -> unit = {
  init_platform (); /* devices */
  init_sys ();      /* processor */
  init_vmem ();     /* virtual memory */

  /* initialize extensions last */
  ext_init ();
  ext_init_regs ();
}
