LEM_DIR?=$(shell opam config var lem:share)

LEMSRC =  \
  ../../src/gen_lib/sail2_instr_kinds.lem \
  ../../src/gen_lib/sail2_values.lem \
  ../../src/gen_lib/sail2_operators.lem \
  ../../src/gen_lib/sail2_operators_mwords.lem \
  ../../src/gen_lib/sail2_operators_bitlists.lem \
  ../../src/gen_lib/sail2_state_monad.lem \
  ../../src/gen_lib/sail2_state.lem \
  ../../src/gen_lib/sail2_string.lem \
  sail2_prompt_monad.lem \
  sail2_prompt.lem \
  sail2_undefined.lem \

SCRIPTS = sail2_instr_kindsScript.sml sail2_valuesScript.sml sail2_operatorsScript.sml \
  sail2_operators_mwordsScript.sml sail2_operators_bitlistsScript.sml \
  sail2_state_monadScript.sml sail2_stateScript.sml \
  sail2_prompt_monadScript.sml sail2_promptScript.sml sail2_undefinedScript.sml \
  sail2_stringScript.sml

THYS = $(patsubst %Script.sml,%Theory.uo,$(SCRIPTS))

all: sail-heap $(THYS)
all-scripts: $(SCRIPTS)

$(SCRIPTS): $(LEMSRC)
	lem -hol -outdir . -auxiliary_level none -lib ../../src/lem_interp -lib ../../src/gen_lib $(LEMSRC)

$(THYS) sail-heap: $(SCRIPTS)
	LEM_DIR=$(LEM_DIR) Holmake

# Holmake will also clear out the generated $(SCRIPTS) files
clean:
	Holmake cleanAll

.PHONY: all all-scripts clean
