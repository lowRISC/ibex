THYS = Sail2_instr_kinds.thy Sail2_values.thy Sail2_operators.thy \
  Sail2_operators_mwords.thy Sail2_operators_bitlists.thy \
  Sail2_state_monad.thy Sail2_state.thy Sail2_state_lifting.thy \
  Sail2_prompt_monad.thy Sail2_prompt.thy Sail2_undefined.thy \
  Sail2_string.thy Sail2_concurrency_interface.thy \
  Sail2_concurrency_interface_mwords.thy \
  Sail2_concurrency_interface_bitlists.thy \
  Sail2_monadic_combinators.thy Sail2_undefined_concurrency_interface.thy
EXTRA_THYS = Sail2_state_monad_lemmas.thy Sail2_state_lemmas.thy \
  Sail2_prompt_monad_lemmas.thy \
  Sail2_operators_mwords_lemmas.thy Hoare.thy \
  Sail2_concurrency_interface_lemmas.thy \
  Sail2_monadic_combinators_lemmas.thy \
  Trace_Properties.thy

LEM_ISA_LIB?=$(shell opam config var lem:share)/isabelle-lib

SAIL_RISCV ?= ../../../sail-riscv

.PHONY: all heap-img clean

all: thys

thys: $(THYS)

heap-img: thys $(EXTRA_THYS) ROOT
	@echo 'Please make sure that the "Word_Lib" entry of the AFP (https://www.isa-afp.org/) is installed'
	@echo 'and set up, e.g. by adding its path to "$$ISABELLE_HOME_USER/ROOTS".'
	if [ -z "$(wildcard $(LEM_ISA_LIB)/ROOT)" ]; \
	then echo isabelle-lib directory of Lem not found. Please set the LEM_ISA_LIB environment variable; false; \
	else isabelle build -b -d $(LEM_ISA_LIB) -D . ; \
	fi

manual: heap-img manual/Manual.thy manual/ROOT manual/document/root.tex
	cp output/document/session_graph.pdf manual/document/Sail_session_graph.pdf
	make -C $(SAIL_RISCV) riscv_duopod
	isabelle build -d $(LEM_ISA_LIB) -d . -d $(SAIL_RISCV)/generated_definitions/isabelle -D manual

Sail2_instr_kinds.thy: ../../src/gen_lib/sail2_instr_kinds.lem
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_values.thy: ../../src/gen_lib/sail2_values.lem Sail2_instr_kinds.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_operators.thy: ../../src/gen_lib/sail2_operators.lem Sail2_values.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_operators_mwords.thy: ../../src/gen_lib/sail2_operators_mwords.lem Sail2_operators.thy Sail2_prompt.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_operators_bitlists.thy: ../../src/gen_lib/sail2_operators_bitlists.lem Sail2_operators.thy Sail2_prompt.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_prompt_monad.thy: ../../src/gen_lib/sail2_prompt_monad.lem Sail2_values.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_prompt.thy: ../../src/gen_lib/sail2_prompt.lem Sail2_prompt_monad.thy Sail2_prompt_monad_lemmas.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_undefined.thy: ../../src/gen_lib/sail2_undefined.lem Sail2_prompt.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_undefined_concurrency_interface.thy: ../../src/gen_lib/sail2_undefined_concurrency_interface.lem Sail2_concurrency_interface.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_state_monad.thy: ../../src/gen_lib/sail2_state_monad.lem Sail2_values.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_state.thy: ../../src/gen_lib/sail2_state.lem Sail2_prompt.thy Sail2_state_monad.thy Sail2_state_monad_lemmas.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_state_lifting.thy: ../../src/gen_lib/sail2_state_lifting.lem Sail2_prompt.thy Sail2_state.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_string.thy: ../../src/gen_lib/sail2_string.lem Sail2_operators_mwords.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_concurrency_interface.thy: ../../src/gen_lib/sail2_concurrency_interface.lem Sail2_string.thy Sail2_values.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_concurrency_interface_mwords.thy: ../../src/gen_lib/sail2_concurrency_interface_mwords.lem Sail2_concurrency_interface.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_concurrency_interface_bitlists.thy: ../../src/gen_lib/sail2_concurrency_interface_bitlists.lem Sail2_concurrency_interface.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

Sail2_monadic_combinators.thy: ../../src/gen_lib/sail2_monadic_combinators.lem Sail2_concurrency_interface.thy Sail2_values.thy
	lem -isa -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $<

clean:
	-rm $(THYS)
