// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "bitfield.h"

// `extern` declarations to give the inline functions in the
// corresponding header a link location.

extern uint32_t bitfield_field32_read(uint32_t bitfield,
                                      bitfield_field32_t field);
extern uint32_t bitfield_field32_write(uint32_t bitfield,
                                       bitfield_field32_t field,
                                       uint32_t value);
extern bool bitfield_bit32_read(uint32_t bitfield,
                                bitfield_bit32_index_t bit_index);
extern uint32_t bitfield_bit32_write(uint32_t bitfield,
                                     bitfield_bit32_index_t bit_index,
                                     bool value);
