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
/*  Copyright (c) 2013-2021                                                 */
/*    Kathyrn Gray                                                          */
/*    Shaked Flur                                                           */
/*    Stephen Kell                                                          */
/*    Gabriel Kerneis                                                       */
/*    Robert Norton-Wright                                                  */
/*    Christopher Pulte                                                     */
/*    Peter Sewell                                                          */
/*    Alasdair Armstrong                                                    */
/*    Brian Campbell                                                        */
/*    Thomas Bauereiss                                                      */
/*    Anthony Fox                                                           */
/*    Jon French                                                            */
/*    Dominic Mulligan                                                      */
/*    Stephen Kell                                                          */
/*    Mark Wassell                                                          */
/*    Alastair Reid (Arm Ltd)                                               */
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
#include <getopt.h>
#include <inttypes.h>
#include <sys/types.h>

#include "sail.h"
#include "rts.h"
#include "elf.h"

#ifdef __cplusplus
extern "C" {
#endif

extern void (*sail_rts_set_coverage_file)(const char *);

static uint64_t g_elf_entry;
uint64_t g_cycle_count = 0;
static uint64_t g_cycle_limit;

extern void model_pre_exit();

unit sail_exit(unit u)
{
  model_pre_exit();
  exit(EXIT_SUCCESS);
  return UNIT;
}

static uint64_t g_verbosity = 0;

fbits sail_get_verbosity(const unit u)
{
  return g_verbosity;
}

bool g_sleeping = false;

unit sleep_request(const unit u)
{
  g_sleeping = true;
  return UNIT;
}

unit wakeup_request(const unit u)
{
  g_sleeping = false;
  return UNIT;
}

bool sleeping(const unit u)
{
    return g_sleeping;
}

/* ***** Sail memory builtins ***** */

/*
 * We organise memory available to the sail model into a linked list
 * of dynamically allocated MASK + 1 size blocks.
 */
struct block {
  uint64_t block_id;
  uint8_t *mem;
  struct block *next;
};

struct block *sail_memory = NULL;

struct tag_block {
  uint64_t block_id;
  bool *mem;
  struct tag_block *next;
};

struct tag_block *sail_tags = NULL;

/*
 * Must be one less than a power of two.
 */
uint64_t MASK = 0xFFFFFFul;

/*
 * All sail vectors are at least 64-bits, but only the bottom 8 bits
 * are used in the second argument.
 */
void write_mem(uint64_t address, uint64_t byte)
{
  uint64_t mask = address & ~MASK;
  uint64_t offset = address & MASK;

  struct block *current = sail_memory;

  while (current != NULL) {
    if (current->block_id == mask) {
      current->mem[offset] = (uint8_t) byte;
      return;
    } else {
      current = current->next;
    }
  }

  /*
   * If we couldn't find a block matching the mask, allocate a new
   * one, write the byte, and put it at the front of the block list.
   */
  struct block *new_block = (struct block *)malloc(sizeof(struct block));
  new_block->block_id = mask;
  new_block->mem = (uint8_t *)calloc(MASK + 1, sizeof(uint8_t));
  new_block->mem[offset] = (uint8_t) byte;
  new_block->next = sail_memory;
  sail_memory = new_block;
}

uint64_t read_mem(uint64_t address)
{
  uint64_t mask = address & ~MASK;
  uint64_t offset = address & MASK;

  struct block *current = sail_memory;

  while (current != NULL) {
    if (current->block_id == mask) {
      return (uint64_t) current->mem[offset];
    } else {
      current = current->next;
    }
  }

  return 0x00;
}

unit write_tag_bool(const uint64_t address, const bool tag)
{
  uint64_t mask = address & ~MASK;
  uint64_t offset = address & MASK;

  struct tag_block *current = sail_tags;

  while (current != NULL) {
    if (current->block_id == mask) {
      current->mem[offset] = tag;
      return UNIT;
    } else {
      current = current->next;
    }
  }

  /*
   * If we couldn't find a block matching the mask, allocate a new
   * one, write the byte, and put it at the front of the block list.
   */
  struct tag_block *new_block = (struct tag_block *)malloc(sizeof(struct tag_block));
  new_block->block_id = mask;
  new_block->mem = (bool *)calloc(MASK + 1, sizeof(bool));
  new_block->mem[offset] = tag;
  new_block->next = sail_tags;
  sail_tags = new_block;

  return UNIT;
}

unit emulator_write_tag(const uint64_t addr_size, const sbits addr, const bool tag)
{
  write_tag_bool(addr.bits, tag);
  return UNIT;
}

bool read_tag_bool(const uint64_t address)
{
  uint64_t mask = address & ~MASK;
  uint64_t offset = address & MASK;

  struct tag_block *current = sail_tags;

  while (current != NULL) {
    if (current->block_id == mask) {
      return current->mem[offset];
    } else {
      current = current->next;
    }
  }

  return false;
}

bool emulator_read_tag(const uint64_t addr_size, const sbits addr)
{
  return read_tag_bool(addr.bits);
}

void kill_mem()
{
  while (sail_memory != NULL) {
    struct block *next = sail_memory->next;

    free(sail_memory->mem);
    free(sail_memory);

    sail_memory = next;
  }

  while (sail_tags != NULL) {
    struct tag_block *next = sail_tags->next;

    free(sail_tags->mem);
    free(sail_tags);

    sail_tags = next;
  }
}

// ***** Memory builtins *****

bool write_ram(const mpz_t addr_size,     // Either 32 or 64
	       const mpz_t data_size_mpz, // Number of bytes
	       const lbits hex_ram,       // Currently unused
	       const lbits addr_bv,
	       const lbits data)
{
  uint64_t addr = mpz_get_ui(*addr_bv.bits);
  uint64_t data_size = mpz_get_ui(data_size_mpz);

  mpz_t buf;
  mpz_init_set(buf, *data.bits);

  uint64_t byte;
  for(uint64_t i = 0; i < data_size; ++i) {
    // Take the 8 low bits of buf and write to addr.
    byte = mpz_get_ui(buf) & 0xFF;
    write_mem(addr + i, byte);

    // Then shift buf 8 bits right.
    mpz_fdiv_q_2exp(buf, buf, 8);
  }

  mpz_clear(buf);
  return true;
}

sbits fast_read_ram(const int64_t data_size,
		    const uint64_t addr)
{
  uint64_t r = 0;

  uint64_t byte;
  for(uint64_t i = (uint64_t) data_size; i > 0; --i) {
    byte = read_mem(addr + (i - 1));
    r = r << 8;
    r = r + byte;
  }
  sbits res = {.len = (uint64_t)data_size * 8, .bits = r };
  return res;
}

void read_ram(lbits *data,
	      const mpz_t addr_size,
	      const mpz_t data_size_mpz,
	      const lbits hex_ram,
	      const lbits addr_bv)
{
  uint64_t addr = mpz_get_ui(*addr_bv.bits);
  uint64_t data_size = mpz_get_ui(data_size_mpz);

  mpz_set_ui(*data->bits, 0);
  data->len = data_size * 8;

  mpz_t byte;
  mpz_init(byte);
  for(uint64_t i = data_size; i > 0; --i) {
    mpz_set_ui(byte, read_mem(addr + (i - 1)));
    mpz_mul_2exp(*data->bits, *data->bits, 8);
    mpz_add(*data->bits, *data->bits, byte);
  }

  mpz_clear(byte);
}

void platform_read_mem(lbits *data,
                       const int read_kind,
                       const uint64_t addr_size,
                       const sbits addr,
                       const mpz_t n)
{
  sbits sdata;
  uint64_t len = mpz_get_ui(n); /* Sail type says always >0 */
  if (len <= 8) {
    /* fast path for small reads */
    sdata = fast_read_ram(len, addr.bits);
    RECREATE_OF(lbits, sbits)(data, sdata, true);
  } else {
    mpz_t mpz_addr_size;
    mpz_init(mpz_addr_size);
    mpz_set_ui(mpz_addr_size, addr_size);
    mpz_t addr_bv;
    mpz_init(addr_bv);
    mpz_set_ui(addr_bv, addr.bits);
    read_ram(data, mpz_addr_size, n, (lbits){.len=0, .bits=NULL}, (lbits){.len=addr.len, .bits=&addr_bv});
    mpz_clear(mpz_addr_size);
    mpz_clear(addr_bv);
  }
}

unit platform_write_mem_ea(const int write_kind,
                           const uint64_t addr_size,
                           const sbits addr,
                           const mpz_t n)
{
    return UNIT;
}

bool platform_write_mem(const int write_kind,
                        const uint64_t addr_size,
                        const sbits addr,
                        const mpz_t n,
                        const lbits data)
{
    mpz_t mpz_addr_size;
    mpz_init(mpz_addr_size);
    mpz_set_ui(mpz_addr_size, addr_size);
    mpz_t addr_bv;
    mpz_init(addr_bv);
    mpz_set_ui(addr_bv, addr.bits);
    bool res = write_ram(mpz_addr_size, n, (lbits){.len=0, .bits=NULL}, (lbits){.len=addr.len, .bits=&addr_bv}, data);
    mpz_clear(mpz_addr_size);
    mpz_clear(addr_bv);
    return res;
}

bool platform_excl_res(const unit unit)
{
    return true;
}

unit platform_barrier()
{
    return UNIT;
}

void emulator_read_mem(lbits *data,
                       const uint64_t addr_size,
                       const sbits addr,
                       const mpz_t n)
{
  platform_read_mem(data, 0, addr_size, addr, n);
}

void emulator_read_mem_ifetch(lbits *data,
                              const uint64_t addr_size,
                              const sbits addr,
                              const mpz_t n)
{
  platform_read_mem(data, 0, addr_size, addr, n);
}

void emulator_read_mem_exclusive(lbits *data,
                                 const uint64_t addr_size,
                                 const sbits addr,
                                 const mpz_t n)
{
  platform_read_mem(data, 0, addr_size, addr, n);
}

bool emulator_write_mem(const uint64_t addr_size,
                        const sbits addr,
                        const mpz_t n,
                        const lbits data)
{
  return platform_write_mem(0, addr_size, addr, n, data);
}

bool emulator_write_mem_exclusive(const uint64_t addr_size,
                                  const sbits addr,
                                  const mpz_t n,
                                  const lbits data)
{
  return platform_write_mem(0, addr_size, addr, n, data);
}

unit load_raw(fbits addr, const_sail_string file)
{
  FILE *fp = fopen(file, "r");

  if (!fp) {
    fprintf(stderr, "[Sail] Raw file %s could not be loaded\n", file);
    exit(EXIT_FAILURE);
  }

  uint64_t byte;
  while ((byte = (uint64_t)fgetc(fp)) != EOF) {
    write_mem(addr, byte);
    addr++;
  }

  return UNIT;
}

void load_image(char *file)
{
  FILE *fp = fopen(file, "r");

  if (!fp) {
    fprintf(stderr, "[Sail] Image file %s could not be loaded\n", file);
    exit(EXIT_FAILURE);
  }

  char *addr = NULL;
  char *data = NULL;
  size_t len = 0;

  while (true) {
    ssize_t addr_len = getline(&addr, &len, fp);
    if (addr_len == -1) break;
    ssize_t data_len = getline(&data, &len, fp);
    if (data_len == -1) break;

    if (!strcmp(addr, "elf_entry\n")) {
      if (sscanf(data, "%" PRIu64 "\n", &g_elf_entry) != 1) {
	fprintf(stderr, "[Sail] Failed to parse elf_entry\n");
        exit(EXIT_FAILURE);
      };
      fprintf(stderr, "[Sail] Elf entry point: %" PRIx64 "\n", g_elf_entry);
    } else {
      write_mem((uint64_t) atoll(addr), (uint64_t) atoll(data));
    }
  }

  free(addr);
  free(data);
  fclose(fp);
}

// ***** Tracing support *****

static int64_t g_trace_depth;
//static int64_t g_trace_max_depth;
static bool g_trace_enabled;

unit enable_tracing(const unit u)
{
  g_trace_depth = 0;
  g_trace_enabled = true;
  return UNIT;
}

unit disable_tracing(const unit u)
{
  g_trace_depth = 0;
  g_trace_enabled = false;
  return UNIT;
}

bool is_tracing(const unit u)
{
  return g_trace_enabled;
}

void trace_fbits(const fbits x) {
  if (g_trace_enabled) fprintf(stderr, "0x%" PRIx64, x);
}

void trace_unit(const unit u) {
  if (g_trace_enabled) fputs("()", stderr);
}

void trace_sail_string(const_sail_string str) {
  if (g_trace_enabled) fputs(str, stderr);
}

void trace_sail_int(const sail_int op) {
  if (g_trace_enabled) mpz_out_str(stderr, 10, op);
}

void trace_lbits(const lbits op) {
  if (g_trace_enabled) fprint_bits("", op, "", stderr);
}

void trace_bool(const bool b) {
  if (g_trace_enabled) {
    if (b) {
      fprintf(stderr, "true");
    } else {
      fprintf(stderr, "false");
    }
  }
}

void trace_unknown(void) {
  if (g_trace_enabled) fputs("?", stderr);
}

void trace_argsep(void) {
  if (g_trace_enabled) fputs(", ", stderr);
}

void trace_argend(void) {
  if (g_trace_enabled) fputs(")\n", stderr);
}

void trace_retend(void) {
  if (g_trace_enabled) fputs("\n", stderr);
}

void trace_start(char *name)
{
  if (g_trace_enabled) {
    fprintf(stderr, "[TRACE] ");
    for (int64_t i = 0; i < g_trace_depth; ++i) {
      fprintf(stderr, "%s", "|   ");
    }
    fprintf(stderr, "%s(", name);
    g_trace_depth++;
  }
}

void trace_end(void)
{
  if (g_trace_enabled) {
    fprintf(stderr, "[TRACE] ");
    for (int64_t i = 0; i < g_trace_depth; ++i) {
      fprintf(stderr, "%s", "|   ");
    }
    g_trace_depth--;
  }
}

/* ***** ELF functions ***** */

void elf_entry(mpz_t *rop, const unit u)
{
  mpz_set_ui(*rop, g_elf_entry);
}

void elf_tohost(mpz_t *rop, const unit u)
{
  mpz_set_ui(*rop, 0x0ul);
}

/* ***** Cycle limit ***** */

/* NB Also increments cycle_count */
bool cycle_limit_reached(const unit u)
{
  return ++g_cycle_count >= g_cycle_limit && g_cycle_limit != 0;
}

unit cycle_count(const unit u)
{
  if (cycle_limit_reached(UNIT)) {
    printf("\n[Sail] TIMEOUT: exceeded %" PRId64 " cycles\n", g_cycle_limit);
    exit(EXIT_SUCCESS);
  }
  return UNIT;
}

void get_cycle_count(sail_int *rop, const unit u)
{
    mpz_set_ui(*rop, g_cycle_count);
}

/* ***** Argument Parsing ***** */

static struct option options[] = {
  {"binary",     required_argument, 0, 'b'},
  {"cyclelimit", required_argument, 0, 'l'},
  {"config",     required_argument, 0, 'C'},
  {"elf",        required_argument, 0, 'e'},
  {"entry",      required_argument, 0, 'n'},
  {"image",      required_argument, 0, 'i'},
  {"coverage",   required_argument, 0, 'c'},
  {"verbosity",  required_argument, 0, 'v'},
  {"help",       no_argument,       0, 'h'},
  {0, 0, 0, 0}
};

static void print_usage()
{
  struct option *opt = options;
  while (opt->name) {
    printf("\t -%c\t %s\n", (char)opt->val, opt->name);
    opt++;
  }
  exit(EXIT_SUCCESS);
}

int process_arguments(int argc, char *argv[])
{
  int c;
  bool     elf_entry_set = false;
  uint64_t elf_entry;

  while (true) {
    int option_index = 0;
    c = getopt_long(argc, argv, "e:n:i:b:l:C:c:v:h", options, &option_index);

    if (c == -1) break;

    switch (c) {
    case 'C': {
        char arg[100];
        uint64_t value;
        if (sscanf(optarg, "%99[a-zA-Z0-9_-.]=0x%" PRIx64, arg, &value) == 2) {
            // do nothing
        } else if (sscanf(optarg, "%99[a-zA-Z0-9_-.]=%" PRId64, arg, &value) == 2) {
            // do nothing
        } else {
          fprintf(stderr, "Could not parse argument %s\n", optarg);
#ifdef HAVE_SETCONFIG
          z__ListConfig(UNIT);
#endif
          return -1;
        };
#ifdef HAVE_SETCONFIG
        mpz_t s_value;
        mpz_init_set_ui(s_value, value);
        z__SetConfig(arg, s_value);
        mpz_clear(s_value);
#else
        fprintf(stderr, "Ignoring flag -C %s", optarg);
#endif
      }
      break;

    case 'b': ;
      uint64_t addr;
      char *cp, *file;

      addr = strtoull(optarg, &cp, 0);
      if (cp == optarg || cp[0] != ',' || cp[1] == '\0') {
	fprintf(stderr, "Could not parse argument %s\n", optarg);
	return -1;
      };
      file = cp + 1;

      load_raw(addr, file);
      break;

    case 'i':
      load_image(optarg);
      break;

    case 'e':
      load_elf(optarg, NULL, &g_elf_entry);
      break;

    case 'n':
      if (!sscanf(optarg, "0x%" PRIx64, &elf_entry)) {
	fprintf(stderr, "Could not parse address %s\n", optarg);
	return -1;
      }
      elf_entry_set = true;
      break;

    case 'l':
      if (!sscanf(optarg, "%" PRId64, &g_cycle_limit)) {
	fprintf(stderr, "Could not parse cycle limit %s\n", optarg);
	return -1;
      }
      break;

    case 'c':
      if (sail_rts_set_coverage_file != NULL) {
        sail_rts_set_coverage_file(optarg);
      } else {
        fprintf(stderr, "Ignoring flag -c %s. Requires the model to be compiled with coverage\n", optarg);
      }
      break;

    case 'v':
      if (!sscanf(optarg, "0x%" PRIx64, &g_verbosity)) {
       fprintf(stderr, "Could not parse verbosity flags %s\n", optarg);
       return -1;
      }
      break;

    case 'h':
      print_usage();
      break;

    default:
      fprintf(stderr, "Unrecognized option %s\n", optarg);
      print_usage();
      return -1;
    }
  }

  // assignment to g_elf_entry is deferred until the end of file so that an
  // explicit command line flag will override the address read from the ELF
  // file.
  if (elf_entry_set) {
      g_elf_entry = elf_entry;
  }

  return 0;
}

/* ***** Setup and cleanup functions for RTS ***** */

void setup_rts(void)
{
  disable_tracing(UNIT);
  setup_library();
}

void cleanup_rts(void)
{
  cleanup_library();
  kill_mem();
}

#ifdef __cplusplus
}
#endif
