
TOP=..
SRCS+=${TOP}/sail-riscv/model/prelude.sail
SRCS+=${TOP}/sail-riscv/model/riscv_xlen32.sail
SRCS+=${TOP}/src/cheri_prelude.sail
SRCS+=${TOP}/src/cheri_types.sail
SRCS+=${TOP}/src/cheri_cap_common.sail
SRCS+=proplib.sail
SRCS+=props.sail
SRCS+=props_setboundsrounddown.sail

SOLVER=z3

auto:
	sail ${SAIL_FLAGS} -smt -smt_auto -smt_auto_solver ${SOLVER} ${SRCS}

manual: generate_smt run_smt

generate_smt:
	sail ${SAIL_FLAGS} -smt ${SRCS}

run_smt:
	@failure=0; \
	for prop in *.smt2; do \
		echo -n "$$prop: "; \
		output=$$($(SOLVER) $$prop); \
		if [ "$$output" = unsat ]; then \
			echo "proved"; \
		elif [ "$$output" = sat ]; then \
			echo "false! Tip: try changing \$$property to \$$counterexample."; \
			failure=1; \
		else \
			echo "Prover said: $$output"; \
			failure=1; \
	fi; done; \
	exit $${failure}

interact:
	sail -i ${SRCS}

clean:
	rm -f *.smt2
