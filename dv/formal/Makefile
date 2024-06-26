SAIL=sail

SAIL_RISCV_MODEL_DIR=../sail-riscv/model

include Sources.mk

PSGEN_SRCS=thm/btype.proof thm/ibex.proof thm/mem.proof thm/riscv.proof
PSGEN_FLAGS=-root riscv -task

SAIL_EXTRA_SRCS=../spec/main.sail

SAIL_SV_FLAGS=-sv -sv-comb -sv-inregs -sv-outregs -sv-nostrings -sv-nopacked -sv-nomem -Oconstant_fold -memo-z3 \
	-sv-unreachable translate -sv-unreachable lookup_TLB -sv-unreachable translate_tlb_miss -sv-unreachable translate_tlb_hit -sv-unreachable pt_walk \
	-sv-fun2wires 2:read_ram \
	-sv-fun2wires 2:write_ram \
	-sv-fun2wires wX \
	-sv-fun2wires 2:rX \

.PHONY: sv
sv:
	mkdir -p build
	python3 buildspec.py header > build/ibexspec_instrs.sv
	cd build && $(SAIL) $(SAIL_SRCS) $(SAIL_EXTRA_SRCS)  $(SAIL_SV_FLAGS) `cd .. && python3 buildspec.py unreachables` -o ibexspec
	python3 spec/fix_pmp_bug.py
	python3 buildspec.py unreachable_loc_hack

.PHONY: reset-sub
reset-sub:
	cd sail-riscv && git reset --hard HEAD

.PHONY: update-sub
update-sub: reset-sub
	cd sail-riscv && git pull

.PHONY: psgen
psgen:
	mkdir -p build
	psgen $(addprefix -path ,$(PSGEN_SRCS)) $(PSGEN_FLAGS) -sv-out build/psgen.sv -tcl-out build/psgen.tcl
