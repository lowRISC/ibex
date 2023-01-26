#include <stdint.h>

#include "encoding.h"

#define get_field(reg, mask) (((reg) & (mask)) / ((mask) & ~((mask) << 1)))
#define set_field(reg, mask, val) (((reg) & ~(mask)) | (((val) * ((mask) & ~((mask) << 1))) & (mask)))

#if __riscv_xlen == 64
# define SATP_PPN SATP64_PPN
typedef uint64_t reg_t;
#else
# define SATP_PPN SATP32_PPN
typedef uint32_t reg_t;
#endif

static char page_buffer[4096 * 6];
static char *page_buffer_next = page_buffer;

typedef struct {
    unsigned mode;
    unsigned levels;
    unsigned ppn_width_bits[5];
    unsigned ppn_offset_bits[5];
    unsigned entry_width_bytes;
    unsigned vpn_width_bits;
    unsigned vaddr_bits;
} virtual_memory_system_t;

static virtual_memory_system_t sv32 = {
    .mode = SATP_MODE_SV32,
    .levels = 2,
    .ppn_width_bits = {12, 10, 10},
    .ppn_offset_bits = {0, 12, 22},
    .entry_width_bytes = 4,
    .vpn_width_bits = 10,
    .vaddr_bits = 32
};

static virtual_memory_system_t sv39 = {
    .mode = SATP_MODE_SV39,
    .levels = 3,
    .ppn_width_bits = {12, 9, 9, 26},
    .ppn_offset_bits = {0, 12, 21, 30},
    .entry_width_bytes = 8,
    .vpn_width_bits = 9,
    .vaddr_bits = 39
};

static virtual_memory_system_t sv48 = {
    .mode = SATP_MODE_SV48,
    .levels = 4,
    .ppn_width_bits = {12, 9, 9, 9, 26},
    .ppn_offset_bits = {0, 12, 21, 30, 39},
    .entry_width_bytes = 8,
    .vpn_width_bits = 9,
    .vaddr_bits = 48
};

static virtual_memory_system_t *vms;

void error()
{
    while (1)
        ;
}

void assert(int condition)
{
    if (!condition)
        error();
}

// Return a 4Kb, aligned, page.
void *get_page()
{
    page_buffer_next = (char *) (((unsigned long) page_buffer_next + 4095) & ~0xfff);
    while (page_buffer_next + 4096 >= page_buffer + sizeof(page_buffer))
        ;
    void *result = page_buffer_next;
    page_buffer_next += 4096;
    return result;
}

reg_t entry(char *table, unsigned index)
{
    if (vms->entry_width_bytes == 4)
        return ((uint32_t *) table)[index];
    else if (vms->entry_width_bytes == 8)
        return ((uint64_t *) table)[index];
    else
        assert(0);
}

void entry_set(char *table, unsigned index, uint64_t value)
{
    if (vms->entry_width_bytes == 4)
        ((uint32_t *) table)[index] = value;
    else if (vms->entry_width_bytes == 8)
        ((uint64_t *) table)[index] = value;
    else
        assert(0);
}

// Set up 1-to-1 for this entire table.
void setup_page_table(char *table, unsigned level, uint64_t physical)
{
    for (unsigned i = 0; i < (1<<vms->vpn_width_bits); i++) {
        uint64_t pte = PTE_V | PTE_R | PTE_W | PTE_X | PTE_U | PTE_A | PTE_D;
        // Add in portion of physical address.
        pte |= physical & (((1LL<<vms->vpn_width_bits)-1) <<
                (PTE_PPN_SHIFT + (level+1) * vms->vpn_width_bits));
        // Add in the index.
        pte |= ((reg_t) i) << (PTE_PPN_SHIFT + level * vms->vpn_width_bits);
        entry_set(table, i, pte);
    }
}

// Return contents of vpn field for the given virtual address and level.
unsigned vpn(uint64_t virtual, unsigned level)
{
    virtual >>= 12 + vms->vpn_width_bits * level;
    return virtual & ((1<<vms->vpn_width_bits)-1);
}
 
// Add an entry to the given table, at the given level (0 for 4Kb page).
void add_entry(char *table, unsigned level, uint64_t virtual, uint64_t physical)
{
    unsigned current_level = vms->levels - 1;
    while (1) {
        unsigned index = vpn(virtual, current_level);
        if (current_level <= level) {
            // Add the new entry.
            entry_set(table, index, PTE_V | PTE_R | PTE_W | PTE_X | PTE_U | PTE_A | PTE_D |
                    ((physical >> 2) & ~((1 <<
                            (PTE_PPN_SHIFT + current_level * vms->vpn_width_bits)) - 1)));
            return;
        }
        reg_t pte = entry(table, index);
        if (!(pte & PTE_V) ||
                ((pte & PTE_R) && (pte & PTE_W))) {
            // Create a new page
            void *new_page = get_page();
            setup_page_table(new_page, current_level - 1, virtual);
            entry_set(table, index, PTE_V |
                    ((((reg_t) new_page) >> 2) & ~((1 << 10) - 1)));
            table = new_page;
        } else {
            table = (char *) (pte & ~0xfff);
        }
        current_level--;
    }
}

int main()
{
    void *master_table = get_page();
    setup_page_table(master_table, vms->levels-1, 0);
    uint32_t *physical = get_page();
    //uint32_t *virtual = (uint32_t *) (((reg_t) physical) ^ ((reg_t) 0x40000000));
    uint32_t *virtual = (uint32_t *) (((reg_t) physical) ^ (((reg_t) 0xf) << (vms->vaddr_bits - 4)));
    // Virtual addresses must be sign-extended.
    if (vms->vaddr_bits < sizeof(virtual) * 8 && (reg_t) virtual & ((reg_t) 1<<(vms->vaddr_bits-1)))
        virtual = (uint32_t *) (
                (reg_t) virtual | ~(((reg_t) 1 << vms->vaddr_bits) - 1));
    add_entry(master_table, 0, (reg_t) virtual, (reg_t) physical);

    unsigned long satp = set_field(0, SATP_MODE, vms->mode);
    satp = set_field(satp, SATP_PPN, ((unsigned long) master_table) >> 12);
    write_csr(satp, satp);
    satp = read_csr(satp);
    if (get_field(satp, SATP_MODE) != vms->mode)
        error();

    reg_t mstatus = read_csr(mstatus);
    mstatus |= MSTATUS_MPRV;
    write_csr(mstatus, mstatus);

    // Address translation is enabled.
    physical[0] = 0xdeadbeef;
    virtual[1] = 0x55667788;
    assert(virtual[0] == 0xdeadbeef);
    assert(physical[0] == 0xdeadbeef);
    assert(virtual[1] == 0x55667788);
    assert(physical[1] == 0x55667788);

active:
end:
    while (1)
        ;
}
