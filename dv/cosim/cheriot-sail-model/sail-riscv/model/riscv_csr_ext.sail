/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

mapping clause csr_name_map = reg <-> hex_bits_12(reg)
end csr_name_map

/* XXX due to an apparent Sail bug the definition of this function must appear
   after the last csr_name_map clause and not by the val spec as it was
   previously. */
function csr_name(csr) = csr_name_map(csr)

function clause ext_is_CSR_defined(_, _) = false
end ext_is_CSR_defined

function clause ext_read_CSR _ = None()
end ext_read_CSR

function clause ext_write_CSR (_, _) = None()
end ext_write_CSR
