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

////////////////////////////////////////////////////////////////
// ELF Loader
////////////////////////////////////////////////////////////////

// Header files for simulator
#include "elf.h"
#include "rts.h"
#include "sail.h"

#ifdef __cplusplus
extern "C" {
#endif

// Define ELF constants/types. These come from the
// Tool Interface Standard Executable and Linking Format Specification 1.2

typedef uint32_t Elf32_Addr;
typedef uint16_t Elf32_Half;
typedef uint32_t Elf32_Off;
typedef uint32_t Elf32_Word;

typedef uint64_t Elf64_Addr;
typedef uint16_t Elf64_Half;
typedef uint64_t Elf64_Off;
typedef uint32_t Elf64_Word;
typedef uint64_t Elf64_Xword;

/* Type for section indices, which are 16-bit quantities.  */
typedef uint16_t Elf32_Section;
typedef uint16_t Elf64_Section;

/* Type for version symbol information.  */
typedef Elf32_Half Elf32_Versym;
typedef Elf64_Half Elf64_Versym;

// Big-Endian support functions which reverse values

uint16_t rev16(uint16_t x) {
    uint16_t a = (x >> 0) & 0xff;
    uint16_t b = (x >> 8) & 0xff;
    return (a << 8) | (b << 0);
}

uint32_t rev32(uint32_t x) {
    uint32_t a = (x >> 0) & 0xff;
    uint32_t b = (x >> 8) & 0xff;
    uint32_t c = (x >> 16) & 0xff;
    uint32_t d = (x >> 24) & 0xff;
    return (a << 24) | (b << 16) | (c << 8) | (d << 0);
}

uint64_t rev64(uint64_t x) {
    uint64_t a = (x >> 0) & 0xff;
    uint64_t b = (x >> 8) & 0xff;
    uint64_t c = (x >> 16) & 0xff;
    uint64_t d = (x >> 24) & 0xff;
    uint64_t e = (x >> 32) & 0xff;
    uint64_t f = (x >> 40) & 0xff;
    uint64_t g = (x >> 48) & 0xff;
    uint64_t h = (x >> 56) & 0xff;
    return (a << 56) | (b << 48) | (c << 40) | (d << 32) | (e << 24) | (f << 16) | (g << 8) | (h << 0);
}

// Endian support macros which reverse values on big-endian machines
// (We assume that the host machine is little-endian)

#define rdAddr32(le, x)  ((le) ? (x) : rev32(x))
#define rdHalf32(le, x)  ((le) ? (x) : rev16(x))
#define rdOff32(le, x)   ((le) ? (x) : rev32(x))
#define rdWord32(le, x)  ((le) ? (x) : rev32(x))

#define rdAddr64(le, x)  ((le) ? (x) : rev64(x))
#define rdHalf64(le, x)  ((le) ? (x) : rev16(x))
#define rdOff64(le, x)   ((le) ? (x) : rev64(x))
#define rdWord64(le, x)  ((le) ? (x) : rev32(x))
#define rdXword64(le, x) ((le) ? (x) : rev64(x))


#define EI_NIDENT      16  /* Size of e_ident */

#define EI_MAG0         0  /* Offsets in e_ident */
#define EI_MAG1         1
#define EI_MAG2         2
#define EI_MAG3         3
#define EI_CLASS        4
#define EI_DATA         5

#define ELFMAG0      0x7f  /* Magic string */
#define ELFMAG1       'E'
#define ELFMAG2       'L'
#define ELFMAG3       'F'

#define ELFCLASS32      1  /* 32-bit ELF */
#define ELFCLASS64      2  /* 64-bit ELF */

#define ELFDATA2LSB     1  /* Little-endian ELF */

#define ET_EXEC         2  /* Executable file */
#define ET_DYN          3  /* Dynamically-linked/Position-independent file */

#define EM_ARM     0x0028  /* 32-bit ARM */
#define EM_AARCH64 0x00B7  /* 64-bit ARM */
#define EM_RISCV   0x00F3  /* RISC-V */
#define EM_X86     0x0003  /* x86 */
#define EM_X86_64  0x003E  /* x86_64 */

#define PT_LOAD         1  /* Loadable segment */

#define SHT_SYMTAB      2  /* Symbol table type */
#define SHT_STRTAB      3  /* String table type */

/* How to extract and insert information held in the st_info field.  */

#define ELF32_ST_BIND(val)        (((unsigned char) (val)) >> 4)
#define ELF32_ST_TYPE(val)        ((val) & 0xf)
#define ELF32_ST_INFO(bind, type) (((bind) << 4) + ((type) & 0xf))

/* Both Elf32_Sym and Elf64_Sym use the same one-byte st_info field.  */
#define ELF64_ST_BIND(val)        ELF32_ST_BIND (val)
#define ELF64_ST_TYPE(val)        ELF32_ST_TYPE (val)
#define ELF64_ST_INFO(bind, type) ELF32_ST_INFO ((bind), (type))


/* Legal values for ST_TYPE subfield of st_info (symbol type).  */

#define STT_NOTYPE     0        /* Symbol type is unspecified */
#define STT_OBJECT     1        /* Symbol is a data object */
#define STT_FUNC       2        /* Symbol is a code object */
#define STT_SECTION    3        /* Symbol associated with a section */
#define STT_FILE       4        /* Symbol's name is file name */
#define STT_COMMON     5        /* Symbol is a common data object */
#define STT_TLS        6        /* Symbol is thread-local data object*/
#define STT_NUM        7        /* Number of defined types.  */
#define STT_LOOS      10        /* Start of OS-specific */
#define STT_GNU_IFUNC 10        /* Symbol is indirect code object */
#define STT_HIOS      12        /* End of OS-specific */
#define STT_LOPROC    13        /* Start of processor-specific */
#define STT_HIPROC    15        /* End of processor-specific */


typedef struct
{
    uint8_t     e_ident[EI_NIDENT]; /* ELF file identifier */
    Elf32_Half  e_type;             /* Object file type */
    Elf32_Half  e_machine;          /* Processor architecture */
    Elf32_Word  e_version;          /* Object file version */
    Elf32_Addr  e_entry;            /* Entry point (loader jumps to this virtual address if != 0) */
    Elf32_Off   e_phoff;            /* Program header table offset */
    Elf32_Off   e_shoff;            /* Section header table offset */
    Elf32_Word  e_flags;            /* Processor-specific flags */
    Elf32_Half  e_ehsize;           /* ELF header size */
    Elf32_Half  e_phentsize;        /* Size of a single program header */
    Elf32_Half  e_phnum;            /* Number of program headers in table */
    Elf32_Half  e_shensize;         /* Size of a single section header */
    Elf32_Half  e_shnum;            /* Number of section headers in table */
    Elf32_Half  e_shtrndx;          /* Index of string table in section header table */
} Elf32_Ehdr;

typedef struct
{
    Elf32_Word  p_type;             /* Segment type */
    Elf32_Off   p_offset;           /* Segment offset in file */
    Elf32_Addr  p_vaddr;            /* Segment load virtual address */
    Elf32_Addr  p_paddr;            /* Segment load physical address */
    Elf32_Word  p_filesz;           /* Segment size in file */
    Elf32_Word  p_memsz;            /* Segment size in memory. Must be >= p_filesz. If > p_filesz, zero pad */
    Elf32_Word  p_flags;            /* Segment flags */
    Elf32_Word  p_align;            /* Segment alignment */
} Elf32_Phdr;

typedef struct
{
    uint8_t     e_ident[EI_NIDENT]; /* ELF file identifier */
    Elf64_Half  e_type;             /* Object file type */
    Elf64_Half  e_machine;          /* Processor architecture */
    Elf64_Word  e_version;          /* Object file version */
    Elf64_Addr  e_entry;            /* Entry point (loader jumps to this virtual address if != 0) */
    Elf64_Off   e_phoff;            /* Program header table offset */
    Elf64_Off   e_shoff;            /* Section header table offset */
    Elf64_Word  e_flags;            /* Processor-specific flags */
    Elf64_Half  e_ehsize;           /* ELF header size */
    Elf64_Half  e_phentsize;        /* Size of a single program header */
    Elf64_Half  e_phnum;            /* Number of program headers in table */
    Elf64_Half  e_shensize;         /* Size of a single section header */
    Elf64_Half  e_shnum;            /* Number of section headers in table */
    Elf64_Half  e_shtrndx;          /* Index of string table in section header table */
} Elf64_Ehdr;

typedef struct
{
    Elf64_Word  p_type;             /* Segment type */
    Elf64_Word  p_flags;            /* Segment flags */
    Elf64_Off   p_offset;           /* Segment offset in file */
    Elf64_Addr  p_vaddr;            /* Segment load virtual address */
    Elf64_Addr  p_paddr;            /* Segment load physical address */
    Elf64_Xword p_filesz;           /* Segment size in file */
    Elf64_Xword p_memsz;            /* Segment size in memory. Must be >= p_filesz.
                                       If > p_filesz, zero pad memory */
    Elf64_Xword p_align;            /* Segment alignment */
} Elf64_Phdr;

typedef struct
{
    Elf32_Word  sh_name;            /* Section name (string tbl index) */
    Elf32_Word  sh_type;            /* Section type */
    Elf32_Word  sh_flags;           /* Section flags */
    Elf32_Addr  sh_addr;            /* Section virtual addr at execution */
    Elf32_Off   sh_offset;          /* Section file offset */
    Elf32_Word  sh_size;            /* Section size in bytes */
    Elf32_Word  sh_link;            /* Link to another section */
    Elf32_Word  sh_info;            /* Additional section information */
    Elf32_Word  sh_addralign;       /* Section alignment */
    Elf32_Word  sh_entsize;         /* Entry size if section holds table */
} Elf32_Shdr;

typedef struct
{
    Elf64_Word  sh_name;            /* Section name (string tbl index) */
    Elf64_Word  sh_type;            /* Section type */
    Elf64_Xword sh_flags;           /* Section flags */
    Elf64_Addr  sh_addr;            /* Section virtual addr at execution */
    Elf64_Off   sh_offset;          /* Section file offset */
    Elf64_Xword sh_size;            /* Section size in bytes */
    Elf64_Word  sh_link;            /* Link to another section */
    Elf64_Word  sh_info;            /* Additional section information */
    Elf64_Xword sh_addralign;       /* Section alignment */
    Elf64_Xword sh_entsize;         /* Entry size if section holds table */
} Elf64_Shdr;

/* Symbol table entry.  */

typedef struct
{
    Elf32_Word    st_name;          /* Symbol name (string tbl index) */
    Elf32_Addr    st_value;         /* Symbol value */
    Elf32_Word    st_size;          /* Symbol size */
    uint8_t       st_info;          /* Symbol type and binding */
    uint8_t       st_other;         /* Symbol visibility */
    Elf32_Section st_shndx;         /* Section index */
} Elf32_Sym;

typedef struct
{
    Elf64_Word    st_name;          /* Symbol name (string tbl index) */
    uint8_t       st_info;          /* Symbol type and binding */
    uint8_t       st_other;         /* Symbol visibility */
    Elf64_Section st_shndx;         /* Section index */
    Elf64_Addr    st_value;         /* Symbol value */
    Elf64_Xword   st_size;          /* Symbol size */
} Elf64_Sym;

void loadBlock32(const char* buffer, Elf32_Off off, Elf32_Addr addr, Elf32_Word filesz, Elf32_Word memsz, const int64_t load_offset) {
    //// std::cout << "Loading block from " << off << " to " << addr << "+:" << filesz << std::endl;
    for(Elf32_Off i = 0; i < filesz; ++i) {
        //// std::cout << "Writing " << (int)buffer[off+i] << " to " << addr+i << std::endl;
        write_mem(load_offset+addr+i, 0xff & buffer[off+i]);
    }
    // Zero fill if p_memsz > p_filesz
    for(Elf32_Off i = filesz; i < memsz; ++i) {
        write_mem(load_offset+addr+i, 0);
    }
}

void loadProgHdr32(bool le, const char* buffer, Elf32_Off off, const int64_t load_offset, const int total_file_size) {
    //// std::cout << "Loading program header at " << off << std::endl;
    if (off > total_file_size - sizeof(Elf32_Phdr)) {
      fprintf(stderr, "Invalid ELF file, section header overruns end of file\n");
      exit(EXIT_FAILURE);
    }
    Elf32_Phdr *phdr = (Elf32_Phdr*) &buffer[off];
    // Only PT_LOAD segments should be loaded;
    if (rdWord32(le, phdr->p_type) == PT_LOAD) {
        Elf32_Off off = rdOff32(le, phdr->p_offset);
        Elf32_Word filesz = rdWord32(le, phdr->p_filesz);
        if (filesz > total_file_size - off) {
	    fprintf(stderr, "Invalid ELF file, section overruns end of file\n");
	    exit(EXIT_FAILURE);
        }
        loadBlock32(buffer, off, rdAddr32(le, phdr->p_paddr), filesz, rdWord32(le, phdr->p_memsz), load_offset);
    }
}

void loadBlock64(const char* buffer, Elf64_Off off, Elf64_Addr addr, Elf64_Word filesz, Elf64_Word memsz, const int64_t load_offset) {
    //// std::cout << "Loading block from " << off << " to " << addr << "+:" << filesz << std::endl;
    for(Elf64_Off i = 0; i < filesz; ++i) {
        // fprintf(stderr, "Writing 0x%x to 0x%lx\n", (int)buffer[off+i], addr+i);
        write_mem(load_offset+addr+i, 0xff & buffer[off+i]);
    }
    // Zero fill if p_memsz > p_filesz
    for(Elf64_Off i = filesz; i < memsz; ++i) {
        write_mem(load_offset+addr+i, 0);
    }
}

void loadProgHdr64(bool le, const char* buffer, Elf64_Off off, const int64_t load_offset, const int total_file_size) {
    //// std::cout << "Loading program header at " << off << std::endl;
    if (off > total_file_size - sizeof(Elf64_Phdr)) {
      fprintf(stderr, "Invalid ELF file, section header overruns end of file\n");
      exit(EXIT_FAILURE);
    }
    Elf64_Phdr *phdr = (Elf64_Phdr*) &buffer[off];
    // Only PT_LOAD segments should be loaded;
    if (rdWord64(le, phdr->p_type) == PT_LOAD) {
        Elf64_Off off = rdOff64(le, phdr->p_offset);
        Elf64_Word filesz = rdXword64(le, phdr->p_filesz);
        if (filesz > total_file_size - off) {
	  fprintf(stderr, "Invalid ELF file, section overruns end of file\n");
	  exit(EXIT_FAILURE);
        }
        loadBlock64(buffer, off, rdAddr64(le, phdr->p_paddr), filesz, rdXword64(le, phdr->p_memsz), load_offset);
    }
}

void checkELFHdr(const char* buffer, const int total_file_size, bool *is_dynamic, bool *is32bit_p) {
    if (total_file_size < sizeof(Elf32_Ehdr)) {
        fprintf(stderr, "File too small, not big enough even for 32-bit ELF header\n");
        exit(EXIT_FAILURE);
    }
    Elf32_Ehdr *hdr = (Elf32_Ehdr*) &buffer[0]; // both Elf32 and Elf64 have same magic
    if (hdr->e_ident[EI_MAG0] != ELFMAG0 ||
        hdr->e_ident[EI_MAG1] != ELFMAG1 ||
        hdr->e_ident[EI_MAG2] != ELFMAG2 ||
        hdr->e_ident[EI_MAG3] != ELFMAG3) {
        fprintf(stderr, "Invalid ELF magic bytes. Not an ELF file?\n");
        exit(EXIT_FAILURE);
    }
    if (hdr->e_ident[EI_CLASS] == ELFCLASS32) {
        bool le = hdr->e_ident[EI_DATA] == ELFDATA2LSB;
        Elf32_Ehdr *ehdr = (Elf32_Ehdr*) &buffer[0];
        if ((rdHalf32(le, ehdr->e_type) != ET_EXEC && rdHalf32(le, ehdr->e_type) != ET_DYN) ||
            (rdHalf32(le, ehdr->e_machine) != EM_ARM &&
             rdHalf64(le, ehdr->e_machine) != EM_RISCV &&
             rdHalf64(le, ehdr->e_machine) != EM_X86)) {
            fprintf(stderr, "Invalid ELF type (0x%x) or machine (0x%x) for class (32-bit)\n",
                    ehdr->e_type, ehdr->e_machine);
            exit(EXIT_FAILURE);
        }
        if (is_dynamic) *is_dynamic = rdHalf32(le, ehdr->e_type) == ET_DYN;
        if (is32bit_p) *is32bit_p = true;
    } else if (hdr->e_ident[EI_CLASS] == ELFCLASS64) {
        if (total_file_size < sizeof(Elf64_Ehdr)) {
            fprintf(stderr, "File too small, specifies 64-bit ELF but not big enough for 64-bit ELF header\n");
            exit(EXIT_FAILURE);
        }
        bool le = hdr->e_ident[EI_DATA] == ELFDATA2LSB;
        Elf64_Ehdr *ehdr = (Elf64_Ehdr*) &buffer[0];
        if ((rdHalf64(le, ehdr->e_type) != ET_EXEC && rdHalf64(le, ehdr->e_type) != ET_DYN) ||
            (rdHalf64(le, ehdr->e_machine) != EM_AARCH64 &&
             rdHalf64(le, ehdr->e_machine) != EM_RISCV &&
             rdHalf64(le, ehdr->e_machine) != EM_X86_64)) {
            fprintf(stderr, "Invalid ELF type (0x%x) or machine (0x%x) for class (64-bit)\n",
                    ehdr->e_type, ehdr->e_machine);
            exit(EXIT_FAILURE);
        }
        if (is_dynamic) *is_dynamic = rdHalf64(le, ehdr->e_type) == ET_DYN;
        if (is32bit_p) *is32bit_p = false;
    } else {
        fprintf(stderr, "Unrecognized ELF file format\n");
        exit(EXIT_FAILURE);
    }
}

void loadELFHdr(const char* buffer, const int total_file_size, bool allow_pie, const int64_t pie_load_offset, bool *is32bit_p, uint64_t *entry) {
    bool is_dynamic;
    checkELFHdr(buffer, total_file_size, &is_dynamic, NULL);
    int64_t load_offset = (allow_pie && is_dynamic) ? pie_load_offset : 0;

    if (!allow_pie && is_dynamic) {
        fprintf(stderr, "Cannot load ET_DYN ELF file\n");
        exit(EXIT_FAILURE);
    }
    Elf32_Ehdr *hdr = (Elf32_Ehdr*) &buffer[0];
    if (hdr->e_ident[EI_CLASS] == ELFCLASS32) {
        bool le = hdr->e_ident[EI_DATA] == ELFDATA2LSB;
        Elf32_Ehdr *ehdr = (Elf32_Ehdr*) &buffer[0];
        for(int i = 0; i < rdHalf32(le, ehdr->e_phnum); ++i) {
            loadProgHdr32(le, buffer, rdOff32(le, ehdr->e_phoff) + i * rdHalf32(le, ehdr->e_phentsize), load_offset, total_file_size);
        }
        if (is32bit_p) *is32bit_p = true;
        if (entry) *entry = (uint64_t) ehdr->e_entry + load_offset;
    } else if (hdr->e_ident[EI_CLASS] == ELFCLASS64) {
        bool le = hdr->e_ident[EI_DATA] == ELFDATA2LSB;
        Elf64_Ehdr *ehdr = (Elf64_Ehdr*) &buffer[0];
        for(int i = 0; i < rdHalf64(le, ehdr->e_phnum); ++i) {
            loadProgHdr64(le, buffer, rdOff64(le, ehdr->e_phoff) + i * rdHalf64(le, ehdr->e_phentsize), load_offset, total_file_size);
        }
        if (is32bit_p) *is32bit_p = false;
        if (entry) *entry = ehdr->e_entry + load_offset;
    } else {
        fprintf(stderr, "Unrecognized ELF file format\n");
        exit(EXIT_FAILURE);
    }
}

void load_elf_at_offset(char *filename, bool allow_pie, const int64_t pie_load_offset, bool *is32bit_p, uint64_t *entry) {
    // Read input file into memory
    char* buffer = NULL;
    int   size   = 0;
    int   chunk  = (1<<24); // increments output buffer this much
    int   read   = 0;
    FILE* in = fopen(filename, "rb");
    if (in == NULL) { goto fail; }
    while (!feof(in)) {
        size = read + chunk;
        buffer = (char*)realloc(buffer, size);
        if (buffer == NULL) { goto fail; }

        int s = fread(buffer+read, 1, size - read, in);
        if (s < 0 || ferror(in)) { goto fail; }
        read += s;
    }
    fclose(in);
    loadELFHdr(buffer, read, allow_pie, pie_load_offset, is32bit_p, entry);
    free(buffer);
    return;

fail:
    fprintf(stderr, "Unable to read file %s\n", filename);
    exit(EXIT_FAILURE);
}

void load_elf(char *filename, bool *is32bit_p, uint64_t *entry) {
    load_elf_at_offset(filename, false, 0, is32bit_p, entry);
}

// symbol lookup for very simple ELF files (single symtab, two strtabs): looks up a
// single symbol at a time, but avoids retaining memory.

int lookupSymbol(const char *buffer, const int total_file_size, const char *symname, uint64_t *value) {
    checkELFHdr(buffer, total_file_size, NULL, NULL);
    Elf32_Ehdr *hdr = (Elf32_Ehdr*) &buffer[0];
    if (hdr->e_ident[EI_CLASS] == ELFCLASS32) {
        bool le = hdr->e_ident[EI_DATA] == ELFDATA2LSB;
        Elf32_Ehdr *ehdr = (Elf32_Ehdr*) &buffer[0];
        if (total_file_size < rdOff32(le, ehdr->e_shoff)
                              + rdHalf32(le, ehdr->e_shnum)*sizeof(Elf32_Shdr)) {
            fprintf(stderr, "File too small for %d sections from offset %ud\n",
                    rdHalf32(le, ehdr->e_shnum), rdOff32(le, ehdr->e_shoff));
            exit(EXIT_FAILURE);
        }
        if (rdHalf32(le, ehdr->e_shtrndx) >= rdHalf32(le, ehdr->e_shnum)) {
            fprintf(stderr, "Invalid string section table index %d\n", hdr->e_shtrndx);
            exit(EXIT_FAILURE);
        }
        Elf32_Shdr *shdr = (Elf32_Shdr *)&buffer[ehdr->e_shoff];
        Elf32_Shdr *shstrtab = (Elf32_Shdr *)&shdr[rdHalf32(le, ehdr->e_shtrndx)];
        if (total_file_size < rdOff32(le, shstrtab->sh_offset) + rdWord32(le, shstrtab->sh_size)) {
            fprintf(stderr, "File too small for string section\n");
            exit(EXIT_FAILURE);
        }
        const char *shstrbuf = buffer + rdOff32(le, shstrtab->sh_offset);
        Elf32_Word strtabidx = 0, symtabidx = 0;
        for (Elf32_Word i = 0; i < rdHalf32(le, ehdr->e_shnum); i++) {
            if (rdWord32(le, shdr[i].sh_type) == SHT_SYMTAB) {
                symtabidx = i;
            }
            if (rdWord32(le, shdr[i].sh_type) == SHT_STRTAB) {
                // skip section name string table
                if (i != rdHalf32(le, ehdr->e_shtrndx)) {
                    strtabidx = i;
                }
            }
        }
        if (!strtabidx || !symtabidx) {
            fprintf(stderr, "ELF: unable to find string or symbol table\n");
            return -1;
        }
        const char *strtab = buffer + rdOff32(le, shdr[strtabidx].sh_offset);
        Elf32_Word strtab_size = rdWord32(le, shdr[strtabidx].sh_size);
        Elf32_Sym *sym_ent = (Elf32_Sym *)(buffer + rdOff32(le, shdr[symtabidx].sh_offset));
        for (Elf32_Word i = 0; i < rdWord32(le, shdr[symtabidx].sh_size)/sizeof(*sym_ent); i++) {
            Elf32_Word sidx = rdWord32(le, sym_ent[i].st_name);
            if (sidx >= strtab_size) {
                fprintf(stderr, "Symbol name index out of bounds\n");
                exit(EXIT_FAILURE);
            }
            Elf32_Word max_len = strtab_size - sidx;
            const char *sname = strtab + sidx;
            if (strnlen(sname, max_len) >= max_len) {
                fprintf(stderr, "Unterminated symbol name\n");
                exit(EXIT_FAILURE);
            }
            if (!strcmp(sname, symname)) {
                if (value) *value = (uint64_t) rdAddr32(le, sym_ent[i].st_value);
                return 0;
            }
        }
        return -1;
    } else if (hdr->e_ident[EI_CLASS] == ELFCLASS64) {
        bool le = hdr->e_ident[EI_DATA] == ELFDATA2LSB;
        Elf64_Ehdr *ehdr = (Elf64_Ehdr*) &buffer[0];
        if (total_file_size < rdOff64(le, ehdr->e_shoff)
                              + rdHalf64(le, ehdr->e_shnum)*sizeof(Elf64_Shdr)) {
	    fprintf(stderr, "File too small for %d sections from offset %" PRIu64 "\n",
                    rdHalf64(le, ehdr->e_shnum), rdOff64(le, ehdr->e_shoff));
            exit(EXIT_FAILURE);
        }
        if (rdHalf64(le, ehdr->e_shtrndx) >= rdHalf64(le, ehdr->e_shnum)) {
            fprintf(stderr, "Invalid string section table index %d\n", hdr->e_shtrndx);
            exit(EXIT_FAILURE);
        }
        Elf64_Shdr *shdr = (Elf64_Shdr *)&buffer[ehdr->e_shoff];
        Elf64_Shdr *shstrtab = (Elf64_Shdr *)&shdr[rdHalf64(le, ehdr->e_shtrndx)];
        if (total_file_size < rdOff64(le, shstrtab->sh_offset) + rdWord64(le, shstrtab->sh_size)) {
            fprintf(stderr, "File too small for string section\n");
            exit(EXIT_FAILURE);
        }
        const char *shstrbuf = buffer + rdOff64(le, shstrtab->sh_offset);
        Elf64_Word strtabidx = 0, symtabidx = 0;
        for (Elf64_Word i = 0; i < rdHalf64(le, ehdr->e_shnum); i++) {
            if (rdWord64(le, shdr[i].sh_type) == SHT_SYMTAB) {
                symtabidx = i;
            }
            if (rdWord64(le, shdr[i].sh_type) == SHT_STRTAB) {
                // skip section name string table
                if (i != rdHalf64(le, ehdr->e_shtrndx)) {
                    strtabidx = i;
                }
            }
        }
        if (!strtabidx || !symtabidx) {
            fprintf(stderr, "ELF: unable to find string or symbol table\n");
            return -1;
        }
        const char *strtab = buffer + rdOff64(le, shdr[strtabidx].sh_offset);
        Elf64_Xword strtab_size = rdXword64(le, shdr[strtabidx].sh_size);
        Elf64_Sym *sym_ent = (Elf64_Sym *)(buffer + rdOff64(le, shdr[symtabidx].sh_offset));
        for (Elf64_Xword i = 0; i < rdXword64(le, shdr[symtabidx].sh_size)/sizeof(*sym_ent); i++) {
            Elf64_Word sidx = rdWord64(le, sym_ent[i].st_name);
            if (sidx >= strtab_size) {
                fprintf(stderr, "Symbol name index out of bounds\n");
                exit(EXIT_FAILURE);
            }
            Elf64_Word max_len = strtab_size - sidx;
            const char *sname = strtab + sidx;
            if (strnlen(sname, max_len) >= max_len) {
                fprintf(stderr, "Unterminated symbol name\n");
                exit(EXIT_FAILURE);
            }
            if (!strcmp(sname, symname)) {
                if (value) *value = (uint64_t) rdAddr64(le, sym_ent[i].st_value);
                return 0;
            }
        }
        return -1;
    } else {
        fprintf(stderr, "Unrecognized ELF file format\n");
        exit(EXIT_FAILURE);
    }
}

int lookup_sym(const char *filename, const char *symname, uint64_t *value) {
    // Read input file into memory
    char* buffer = NULL;
    int   size   = 0;
    int   chunk  = (1<<24); // increments output buffer this much
    int   read   = 0;
    int   ret    = 0;
    FILE* in = fopen(filename, "rb");
    if (in == NULL) { goto fail; }
    while (!feof(in)) {
        size = read + chunk;
        buffer = (char*)realloc(buffer, size);
        if (buffer == NULL) { goto fail; }

        int s = fread(buffer+read, 1, size - read, in);
        if (s < 0) { goto fail; }
        read += s;
    }
    fclose(in);
    ret = lookupSymbol(buffer, read, symname, value);
    free(buffer);
    return ret;

fail:
    fprintf(stderr, "Unable to read file %s\n", filename);
    exit(EXIT_FAILURE);
}

////////////////////////////////////////////////////////////////
// ELF Loader
////////////////////////////////////////////////////////////////

#ifdef __cplusplus
}
#endif
