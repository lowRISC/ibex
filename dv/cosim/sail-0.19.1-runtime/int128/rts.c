#include<string.h>
#include<getopt.h>
#include<inttypes.h>

#include"sail.h"
#include"rts.h"
#include"elf.h"

static uint64_t g_elf_entry;
uint64_t g_cycle_count = 0;
static uint64_t g_cycle_limit;

void sail_match_failure(const_sail_string msg)
{
  fprintf(stderr, "Pattern match failure in %s\n", msg);
  exit(EXIT_FAILURE);
}

unit sail_assert(bool b, const_sail_string msg)
{
  if (b) return UNIT;
  fprintf(stderr, "Assertion failed: %s\n", msg);
  exit(EXIT_FAILURE);
}

unit sail_exit(unit u)
{
  fprintf(stderr, "[Sail] Exiting after %" PRIu64 " cycles\n", g_cycle_count);
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
  fprintf(stderr, "Sail CPU model going to sleep\n");
  g_sleeping = true;
  return UNIT;
}

unit wakeup_request(const unit u)
{
  fprintf(stderr, "Sail CPU model waking up\n");
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

  //if ((byte >= 97 && byte <= 122) || (byte >= 64 && byte <= 90) || (byte >= 48 && byte <= 57) || byte == 10 || byte == 32) {
  //  fprintf(stderr, "%c", (char) byte);
  //}

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
  fprintf(stderr, "[Sail] Allocating new block 0x%" PRIx64 "\n", mask);
  struct block *new_block = malloc(sizeof(struct block));
  new_block->block_id = mask;
  new_block->mem = calloc(MASK + 1, sizeof(uint8_t));
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
  fprintf(stderr, "[Sail] Allocating new tag block 0x%" PRIx64 "\n", mask);
  struct tag_block *new_block = malloc(sizeof(struct tag_block));
  new_block->block_id = mask;
  new_block->mem = calloc(MASK + 1, sizeof(bool));
  new_block->mem[offset] = tag;
  new_block->next = sail_tags;
  sail_tags = new_block;

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

mpz_t write_buf;

bool write_ram(const sail_int addr_size,     // Either 32 or 64
	       const sail_int data_size_mpz, // Number of bytes
	       const lbits hex_ram,          // Currently unused
	       const lbits addr_bv,
	       const lbits data)
{
  uint64_t addr = mpz_get_ui(*addr_bv.bits);
  uint64_t data_size = (uint64_t) data_size_mpz;

  if (data_size <= 8) {
    uint64_t bytes = mpz_get_ui(*data.bits);

    for(uint64_t i = 0; i < data_size; ++i) {
      write_mem(addr + i, bytes & 0xFF);
      bytes >>= 8;
    }

    return true;
  } else {
    mpz_set(write_buf, *data.bits);

    uint64_t byte;
    for(uint64_t i = 0; i < data_size; ++i) {
      // Take the 8 low bits of write_buf and write to addr.
      byte = mpz_get_ui(write_buf) & 0xFF;
      write_mem(addr + i, byte);

      // Then shift buf 8 bits right.
      mpz_fdiv_q_2exp(write_buf, write_buf, 8);
    }
    
    return true;
  }
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
  sbits res = {.len = data_size * 8, .bits = r };
  return res;
}

mpz_t read_buf;

void read_ram(lbits *data,
	      const sail_int addr_size,
	      const sail_int data_size_mpz,
	      const lbits hex_ram,
	      const lbits addr_bv)
{
  uint64_t addr = mpz_get_ui(*addr_bv.bits);
  uint64_t data_size = (uint64_t) data_size_mpz;

  if (data_size <= 8) {
    uint64_t byte = 0;

    for(uint64_t i = data_size; i > 0; --i) {
      byte = byte << 8;
      byte += read_mem(addr + (i - 1));
    }

    mpz_set_ui(*data->bits, byte);
    data->len = data_size * 8;
  } else {
    mpz_set_ui(*data->bits, 0);
    data->len = data_size * 8;

    for(uint64_t i = data_size; i > 0; --i) {
      mpz_set_ui(read_buf, read_mem(addr + (i - 1)));
      mpz_mul_2exp(*data->bits, *data->bits, 8);
      mpz_add(*data->bits, *data->bits, read_buf);
    }
  }
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

/* ***** ELF functions ***** */

sail_int elf_entry(const unit u)
{
  return (__int128) g_elf_entry;
}

sail_int elf_tohost(const unit u)
{
  return (__int128) 0;
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

sail_int get_cycle_count(const unit u)
{
  return (__int128) g_cycle_count;
}

/* ***** Argument Parsing ***** */

static struct option options[] = {
  {"binary",     required_argument, 0, 'b'},
  {"cyclelimit", required_argument, 0, 'l'},
  {"config",     required_argument, 0, 'C'},
  {"elf",        required_argument, 0, 'e'},
  {"entry",      required_argument, 0, 'n'},
  {"image",      required_argument, 0, 'i'},
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
    c = getopt_long(argc, argv, "e:n:i:b:l:C:h", options, &option_index);

    if (c == -1) break;

    switch (c) {
    case 'C': {
        char arg[100];
        uint64_t value;
        if (sscanf(optarg, "%99[a-zA-Z0-9_-.]=0x%" PRIx64, arg, &value) == 2) {
            // fprintf(stderr, "Got hex flag %s %" PRIx64 "\n", arg, value);
            // do nothing
        } else if (sscanf(optarg, "%99[a-zA-Z0-9_-.]=%" PRId64, arg, &value) == 2) {
            // fprintf(stderr, "Got decimal flag %s %" PRIx64 "\n", arg, value);
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
      load_elf(optarg, NULL, NULL);
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
  mpz_init(write_buf);
  mpz_init(read_buf);
  return;
}

void cleanup_rts(void)
{
  mpz_clear(write_buf);
  mpz_clear(read_buf);
  kill_mem();
}
