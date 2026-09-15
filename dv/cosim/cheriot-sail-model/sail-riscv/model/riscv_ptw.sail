/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* failure modes for address-translation/page-table-walks */

union PTW_Error = {
  PTW_Invalid_Addr  : unit,          /* invalid source address */
  PTW_Access        : unit,          /* physical memory access error for a PTE */
  PTW_Invalid_PTE   : unit,
  PTW_No_Permission : unit,
  PTW_Misaligned    : unit,          /* misaligned superpage */
  PTW_PTE_Update    : unit,          /* PTE update needed but not enabled */
  PTW_Ext_Error     : ext_ptw_error  /* parameterized for errors from extensions */
}

val ptw_error_to_str : PTW_Error -> string
function ptw_error_to_str(e) =
  match (e) {
    PTW_Invalid_Addr()   => "invalid-source-addr",
    PTW_Access()         => "mem-access-error",
    PTW_Invalid_PTE()    => "invalid-pte",
    PTW_No_Permission()  => "no-permission",
    PTW_Misaligned()     => "misaligned-superpage",
    PTW_PTE_Update()     => "pte-update-needed",
    PTW_Ext_Error(e)     => "extension-error"
  }

overload to_str = {ptw_error_to_str}

/* hook for extensions to customize errors reported by page-table
 * walks during address translation; it typically works in conjunction
 * with any customization to checkPTEPermission().
 */
function ext_get_ptw_error(eptwf : ext_ptw_fail) -> PTW_Error =
  PTW_No_Permission()

/* conversion of these translation/PTW failures into architectural exceptions */
function translationException(a : AccessType(ext_access_type), f : PTW_Error) -> ExceptionType = {
  let e : ExceptionType =
  match (a, f) {
    (_, PTW_Ext_Error(e))        => E_Extension(ext_translate_exception(e)),
    (ReadWrite(_), PTW_Access()) => E_SAMO_Access_Fault(),
    (ReadWrite(_), _)            => E_SAMO_Page_Fault(),
    (Read(_), PTW_Access())      => E_Load_Access_Fault(),
    (Read(_), _)                 => E_Load_Page_Fault(),
    (Write(_), PTW_Access())     => E_SAMO_Access_Fault(),
    (Write(_), _)                => E_SAMO_Page_Fault(),
    (Execute(), PTW_Access())    => E_Fetch_Access_Fault(),
    (Execute(), _)               => E_Fetch_Page_Fault()
  } in {
/*  print_mem("translationException(" ^ a ^ ", " ^ f ^ ") -> " ^ e); */
    e
  }
}
