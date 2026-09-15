/****************************************************************************/
/*     Sail                                                                 */
/*                                                                          */
/*  Sail and the Sail architecture models here, comprising all files and    */
/*  directories except the ASL-derived Sail code in the aarch64 directory,  */
/*  are subject to the BSD two-clause licence below.                        */
/*                                                                          */
/*  The ASL derived parts of the ARMv8.3 specification in                   */
/*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               */
/*                                                                          */
/*  Copyright (c) 2024-2025                                                 */
/*    Alasdair Armstrong                                                    */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This work was partially supported by EPSRC grant EP/K008528/1 <a        */
/*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          */
/*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   */
/*  KTF funding, and donations from Arm.  This project has received         */
/*  funding from the European Research Council (ERC) under the European     */
/*  Union’s Horizon 2020 research and innovation programme (grant           */
/*  agreement No 789108, ELVER).                                            */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        */
/*  and FA8750-10-C-0237 ("CTSRD").                                         */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/****************************************************************************/

#ifndef SAIL_CONFIG_H
#define SAIL_CONFIG_H

/*
 * This file implements the runtime configuration of a Sail model
 * using a JSON configuration file.
 *
 * It abstracts away the particular details of the exact JSON library
 * that is being used.
 */

#include "sail.h"
#include "sail_failure.h"
#include "cJSON.h"

#ifdef __cplusplus
extern "C" {
#endif

struct sail_json;

typedef const_sail_string sail_config_key[];

typedef struct sail_json* sail_config_json;

/*
 * Load the runtime JSON config from a null-terminated
 * string containing JSON data.
 */
 void sail_config_set_string(const char *json);

/*
 * Load the runtime JSON config from a file. The file
 * is read into memory and closed so it does not need
 * to exist after this function returns.
 */
void sail_config_set_file(const char *path);

/*
 * Deallocate any memory used by the configuration.
 *
 * After using this, other functions in this module are no long safe to call.
 */
void sail_config_cleanup(void);

/*
 * Get the JSON corresponding to some key.
 */
sail_config_json sail_config_get(const size_t n, const_sail_string const *key);

/*
 * Get the JSON corresponding to some key. Rather than an array the
 * key is a string with '.' characters separating the parts. Returns
 * NULL if the key cannot be found.
 */
sail_config_json sail_config_lookup(const char *dotted_key);

/*
 * For each Sail type, Sail will generate code that will destructure
 * the JSON values using the following function calls.
 *
 * In general, it will test if the JSON is the type it expects, and
 * only then access the fields. The behaviour of these functions is
 * not guaranteed if the JSON does not have the correct type.
 */

bool sail_config_is_object(const sail_config_json config);
bool sail_config_object_has_key(const sail_config_json config, const_sail_string key);
sail_config_json sail_config_object_key(const sail_config_json config, const_sail_string key);

int64_t sail_config_list_length(const sail_config_json config);
sail_config_json sail_config_list_nth(const sail_config_json config, int64_t index);

bool sail_config_is_array(const sail_config_json config);
bool sail_config_is_bits(const sail_config_json config);
bool sail_config_is_bool(const sail_config_json config);
bool sail_config_is_bool_array(const sail_config_json config);
bool sail_config_is_int(const sail_config_json config);
bool sail_config_is_string(const sail_config_json config);

void sail_config_unwrap_bit(lbits *bv, const sail_config_json config);
void sail_config_unwrap_bits(lbits *bv, const sail_config_json config);
bool sail_config_unwrap_bool(const sail_config_json config);
void sail_config_unwrap_int(sail_int *n, const sail_config_json config);
void sail_config_unwrap_string(sail_string *str, const sail_config_json config);

/*
 * Configurable abstract types require some special handling.
 *
 * Their length will be a string value like "xlen" or "mxlen". It is
 * up to the user of this API to detect this and use the
 * `unwrap_abstract_bits` variant after finding the correct width.
 */
bool sail_config_is_bits_abstract(const sail_config_json config);
void sail_config_bits_abstract_len(sail_string *str, const sail_config_json config);
void sail_config_unwrap_abstract_bits(lbits *bv, int64_t len, sail_config_json config);

#ifdef __cplusplus
}
#endif

#endif
