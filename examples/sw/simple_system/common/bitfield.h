// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SIMPLE_SYSTEM_COMMON_BITFIELD_H_
#define SIMPLE_SYSTEM_COMMON_BITFIELD_H_

#include <stdbool.h>
#include <stdint.h>

/**
 * A field of a 32-bit bitfield.
 *
 * The following field definition: `{ .mask = 0b11, .index = 12 }`
 *
 * Denotes the X-marked bits in the following 32-bit bitfield:
 *
 *     field:  0b--------'--------'--XX----'--------
 *     index:   31                                 0
 *
 * Restrictions: The index plus the width of the mask must not be greater than
 * 31.
 */
typedef struct bitfield_field32 {
  /** The field mask. Usually all ones. */
  uint32_t mask;
  /** The field position in the bitfield, counting from the zero-bit. */
  uint32_t index;
} bitfield_field32_t;

/**
 * A single bit in a 32-bit bitfield.
 *
 * This denotes the position of a single bit, counting from the zero-bit.
 *
 * For instance, `(bitfield_bit_index_t)4` denotes the X-marked bit in the
 * following 32-bit bitfield:
 *
 *     field:  0b--------'--------'--------'---X----
 *     index:   31                                 0
 *
 * Restrictions: The value must not be greater than 31.
 */
typedef uint32_t bitfield_bit32_index_t;

/**
 * Turns a `bitfield_bit32_index_t` into a `bitfield_field32_t` (which is more
 * general).
 *
 * @param bit_index The corresponding single bit to turn into a field.
 * @return A 1-bit field that corresponds to `bit_index`.
 */
inline bitfield_field32_t bitfield_bit32_to_field32(
    bitfield_bit32_index_t bit_index) {
  return (bitfield_field32_t){
      .mask = 0x1, .index = bit_index,
  };
}

/**
 * Reads a value from `field` in `bitfield`.
 *
 * This function uses the `field` parameter to read the value from `bitfield`.
 * The resulting value will be shifted right and zero-extended so the field's
 * zero-bit is the return value's zero-bit.
 *
 * @param bitfield Bitfield to get the field from.
 * @param field Field to read out from.
 * @return Zero-extended `field` from `bitfield`.
 */
inline uint32_t bitfield_field32_read(uint32_t bitfield,
                                      bitfield_field32_t field) {
  return (bitfield >> field.index) & field.mask;
}

/**
 * Writes `value` to `field` in `bitfield`.
 *
 * This function uses the `field` parameter to set specific bits in `bitfield`.
 * The relevant portion of `bitfield` is zeroed before the bits are set to
 * `value`.
 *
 * @param bitfield Bitfield to set the field in.
 * @param field Field within bitfield to be set.
 * @param value Value for the new field.
 * @return `bitfield` with `field` set to `value`.
 */
inline uint32_t bitfield_field32_write(uint32_t bitfield,
                                       bitfield_field32_t field,
                                       uint32_t value) {
  bitfield &= ~(field.mask << field.index);
  bitfield |= (value & field.mask) << field.index;
  return bitfield;
}

/**
 * Writes `value` to the `bit_index`th bit in `bitfield`.
 *
 * @param bitfield Bitfield to update the bit in.
 * @param bit_index Bit to update.
 * @param value Bit value to write to `bitfield`.
 * @return `bitfield` with the `bit_index`th bit set to `value`.
 */
inline uint32_t bitfield_bit32_write(uint32_t bitfield,
                                     bitfield_bit32_index_t bit_index,
                                     bool value) {
  return bitfield_field32_write(bitfield, bitfield_bit32_to_field32(bit_index),
                                value ? 0x1u : 0x0u);
}

/**
 * Reads the `bit_index`th bit in `bitfield`.
 *
 * @param bitfield Bitfield to get the bit from.
 * @param bit_index Bit to read.
 * @return `true` if the bit was one, `false` otherwise.
 */
inline bool bitfield_bit32_read(uint32_t bitfield,
                                bitfield_bit32_index_t bit_index) {
  return bitfield_field32_read(bitfield,
                               bitfield_bit32_to_field32(bit_index)) == 0x1u;
}

#endif  // SIMPLE_SYSTEM_COMMON_BITFIELD_H_
