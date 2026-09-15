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
/*  Copyright (c) 2024                                                      */
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

#include <string.h>

#include "sail_config.h"
#include "cJSON.h"

#ifdef __cplusplus
extern "C" {
#endif

struct sail_json
{
  cJSON json;
};

typedef struct sail_json* sail_config_json;

static cJSON *sail_config;

void sail_config_set_string(const char *json)
{
  cJSON_Hooks hooks;
  hooks.malloc_fn = &sail_malloc;
  hooks.free_fn = &sail_free;
  cJSON_InitHooks(&hooks);

  // Points to the position of a parse error if there was one.
  const char *parse_end = json;

  // Parse the JSON. Setting `require_null_terminated` to 1 enables
  // two conflated checks: that the input is null terminated (which
  // we guarantee above), and that there is no junk data after the JSON.
  sail_config = cJSON_ParseWithOpts(json, &parse_end, 1);

  if (!sail_config) {
    char error_message[128];
    snprintf(error_message, sizeof error_message, "Failed to parse JSON configuration at offset %ld", parse_end - json);
    sail_assert(false, error_message);
  }
}

void sail_config_set_file(const char *path)
{
  FILE *f = fopen(path, "rb");
  fseek(f, 0, SEEK_END);
  long fsize = ftell(f);
  fseek(f, 0, SEEK_SET);

  char *buffer = (char *)sail_malloc(fsize + 1);

  size_t ret_size = fread(buffer, fsize, 1, f);

  if (ret_size != 1) {
    sail_assert(false, "Failed to read configuration");
  }

  buffer[fsize] = 0;
  fclose(f);

  // Check there are no null bytes in the file because
  // sail_config_set_string() relies on null termination
  // to find the end of the string.
  for (size_t i = 0; i < fsize; ++i) {
    sail_assert(buffer[i] != 0, "Null byte in JSON configuration");
  }

  sail_config_set_string(buffer);

  sail_free(buffer);
}

void sail_config_cleanup(void)
{
  cJSON_Delete((cJSON *)sail_config);
}

sail_config_json sail_config_get(size_t n, const_sail_string const *key)
{
  sail_config_json result;
  cJSON *json = (cJSON *)sail_config;

  for (int i = 0; i < n; i++) {
    if (cJSON_IsObject(json)) {
      json = cJSON_GetObjectItemCaseSensitive(json, key[i]);
    } else {
      fprintf(stderr, "Failed to access configuration item: '");
      for (int j = 0; j < n; j++) {
        fprintf(stderr, ".%s", key[j]);
      }
      fprintf(stderr, "'\n");
      exit(EXIT_FAILURE);
    }
  }

  return (sail_config_json)json;
}

sail_config_json sail_config_lookup(const char *dotted_key)
{
  sail_config_json result;
  cJSON *json = (cJSON *)sail_config;

  size_t start = 0;
  size_t len = strlen(dotted_key);

  for (size_t i = 0; i <= len; i++) {
    if (dotted_key[i] == '.' || dotted_key[i] == '\0') {
      char *key = (char *)sail_malloc((i - start) + 1);
      strncpy(key, dotted_key + start, i - start);
      key[i - start] = '\0';
      start = i + 1;

      if (cJSON_IsObject(json)) {
        json = cJSON_GetObjectItemCaseSensitive(json, key);
      } else {
        json = NULL;
        break;
      }
    }
  }

  return (sail_config_json)json;
}

int64_t sail_config_list_length(const sail_config_json config)
{
  cJSON *json = (cJSON *)config;

  if (cJSON_IsArray(json)) {
    return (int64_t)cJSON_GetArraySize(json);
  } else {
    return INT64_C(-1);
  }
}

sail_config_json sail_config_list_nth(const sail_config_json config, int64_t index)
{
  // This is very inefficient, but works with how the Jib IR functions
  cJSON *json = (cJSON *)config;
  cJSON *item = cJSON_GetArrayItem(json, (int)index);
  return (sail_config_json)item;
}

bool sail_config_is_bool(const sail_config_json config)
{
  return cJSON_IsBool((cJSON *)config);
}

bool sail_config_unwrap_bool(const sail_config_json config)
{
  return cJSON_IsTrue((cJSON *)config);
}

bool sail_config_is_object(const sail_config_json config)
{
  return cJSON_IsObject((cJSON *)config);
}

bool sail_config_object_has_key(const sail_config_json config, const_sail_string key)
{
  return cJSON_HasObjectItem((cJSON *)config, key);
}

sail_config_json sail_config_object_key(const sail_config_json config, const_sail_string key)
{
  return (sail_config_json)cJSON_GetObjectItemCaseSensitive((cJSON *)config, key);
}

bool sail_config_is_string(const sail_config_json config)
{
  return cJSON_IsString((cJSON *)config);
}

bool sail_config_is_int(const sail_config_json config)
{
  return cJSON_IsNumber((cJSON *)config);
}

bool sail_config_is_array(const sail_config_json config)
{
  return cJSON_IsArray((cJSON *)config);
}

bool sail_config_is_bool_array(const sail_config_json config)
{
  if (!sail_config_is_array(config)) {
    return false;
  }

  int len = cJSON_GetArraySize((cJSON *)config);

  cJSON *value;
  cJSON_ArrayForEach(value, ((cJSON*)config)) {
    if (!cJSON_IsBool(value)) {
      return false;
    }
  }

  return true;
}

bool sail_config_is_bits(const sail_config_json config)
{
  bool is_bool_array = sail_config_is_bool_array(config);

  bool is_bv_object = sail_config_is_object(config);
  if (is_bv_object) {
    is_bv_object &= sail_config_object_has_key(config, "len");
    is_bv_object &= sail_config_object_has_key(config, "value");
  }

  return is_bool_array || is_bv_object;
}

bool sail_config_is_bits_abstract(const sail_config_json config)
{
  cJSON *json = (cJSON *)config;

  if (!(cJSON_IsObject(json) && cJSON_HasObjectItem(json, "len"))) {
    return false;
  }

  return cJSON_IsString(cJSON_GetObjectItemCaseSensitive(json, "len"));
}

void sail_config_bits_abstract_len(sail_string *str, const sail_config_json config)
{
  cJSON *json = (cJSON *)config;

  cJSON *len_json = cJSON_GetObjectItemCaseSensitive(json, "len");
  sail_string len_str = cJSON_GetStringValue(len_json);

  size_t sz = strlen(len_str);
  *str = (sail_string)realloc(*str, sz + 1);
  *str = strcpy(*str, len_str);
}

void sail_config_unwrap_string(sail_string *str, const sail_config_json config)
{
  sail_string conf_str = cJSON_GetStringValue((cJSON *)config);

  size_t len = strlen(conf_str);
  *str = (sail_string)realloc(*str, len + 1);
  *str = strcpy(*str, conf_str);
}

void sail_config_unwrap_int(sail_int *n, const sail_config_json config)
{
  cJSON *json = (cJSON *)config;
  if (mpz_set_str(*n, json->valuestring, 10) == -1) {
    sail_assert(false, "Failed to parse integer from configuration");
  }
}

void sail_config_truncate(lbits *rop) {
  mpz_t tmp;
  mpz_init(tmp);

  mpz_set_ui(tmp, 1);
  mpz_mul_2exp(tmp, tmp, rop->len);
  mpz_sub_ui(tmp, tmp, 1);
  mpz_and(*rop->bits, *rop->bits, tmp);

  mpz_clear(tmp);
}

void sail_config_unwrap_bit(lbits *bv, const sail_config_json config)
{
  cJSON *json = (cJSON *)config;

  bv->len = 1;
  if (cJSON_IsTrue(json)) {
    mpz_set_ui(*bv->bits, 1);
  } else {
    mpz_set_ui(*bv->bits, 0);
  }
}

void sail_config_set_bits_value(lbits *bv, char *v)
{
  size_t i = 0;
  for (char *c = v; *c != '\0'; c++) {
    if (*c != '_') {
      v[i] = *c;
      i++;
    }
  }
  v[i] = '\0';

  if (strncmp(v, "0x", 2) == 0) {
    gmp_sscanf(v, "0x%Zx", bv->bits);
  } else if (strncmp(v, "0b", 2) == 0) {
    mp_bitcnt_t b = 0;
    i--;
    do {
      if (v[i] == '1') {
        mpz_setbit(*bv->bits, b);
      }
      b++;
      i--;
    } while (i >= 2);
  } else {
    gmp_sscanf(v, "%Zd", bv->bits);
  }

  sail_config_truncate(bv);
}

void sail_config_unwrap_abstract_bits(lbits *bv, int64_t len, sail_config_json config)
{
  cJSON *json = (cJSON *)config;
  cJSON *value_json = cJSON_GetObjectItemCaseSensitive(json, "value");
  char *v = value_json->valuestring;

  bv->len = (mp_bitcnt_t)len;

  sail_config_set_bits_value(bv, v);
}

void sail_config_unwrap_bits(lbits *bv, const sail_config_json config)
{
  cJSON *json = (cJSON *)config;

  if (cJSON_IsArray(json)) {
    mp_bitcnt_t len = (mp_bitcnt_t)cJSON_GetArraySize(json);
    bv->len = len;
    mpz_set_ui(*bv->bits, 0);

    mp_bitcnt_t i = 0;
    cJSON *bit;
    cJSON_ArrayForEach(bit, json) {
      if (cJSON_IsTrue(bit)) {
        mpz_setbit(*bv->bits, len - i - 1);
      }
      i++;
    }
  } else {
    cJSON *len_json = cJSON_GetObjectItemCaseSensitive(json, "len");
    cJSON *value_json = cJSON_GetObjectItemCaseSensitive(json, "value");
    char *v = value_json->valuestring;
    bool has_separator = false;

    if (cJSON_IsNumber(len_json)) {
      bv->len = (mp_bitcnt_t)atoi(len_json->valuestring);
    } else {
      bv->len = 32;
    }

    sail_config_set_bits_value(bv, v);
  }
}

#ifdef __cplusplus
}
#endif
