
# Attempt to work with either sail from opam or built from repo in SAIL_DIR
ifneq ($(SAIL_DIR),)
# Use sail repo in SAIL_DIR
SAIL:=$(SAIL_DIR)/sail
export SAIL_DIR
else
# Use sail from opam package
SAIL_DIR=$(shell opam config var sail:share)
SAIL:=sail
endif
SAIL_LIB_DIR:=$(SAIL_DIR)/lib
export SAIL_LIB_DIR
SAIL_SRC_DIR:=$(SAIL_DIR)/src

ARCH=RV32

QTEST_BUILD=qtest_build

SAIL_RISCV_DIR=../sail-riscv
SAIL_RISCV_MODEL_DIR=$(SAIL_RISCV_DIR)/model
SAIL_CHERI_MODEL_DIR=../src

SAIL_RV32_XLEN := $(SAIL_RISCV_MODEL_DIR)/riscv_xlen32.sail
CHERI_CAP_RV32_IMPL := cheri_prelude_64.sail

SAIL_RV64_XLEN := $(SAIL_RISCV_MODEL_DIR)/riscv_xlen64.sail
CHERI_CAP_RV64_IMPL := cheri_prelude_128.sail

SAIL_XLEN = $(SAIL_$(ARCH)_XLEN)
CHERI_CAP_IMPL = $(CHERI_CAP_$(ARCH)_IMPL)

QTEST_SAIL_FILES=$(SAIL_RISCV_MODEL_DIR)/prelude.sail \
          $(SAIL_XLEN) \
          $(SAIL_CHERI_MODEL_DIR)/cheri_prelude.sail \
          $(SAIL_CHERI_MODEL_DIR)/cheri_types.sail \
          $(SAIL_CHERI_MODEL_DIR)/$(CHERI_CAP_IMPL) \
          $(SAIL_CHERI_MODEL_DIR)/cheri_cap_common.sail

QTEST_BUILD=qtest_build

all: qtest

$(QTEST_BUILD): $(QTEST_SAIL_FILES)
	$(SAIL) -ocaml -ocaml-nobuild -ocaml_build_dir $@ -o cheri_cc $^

$(QTEST_BUILD)/main.native: $(QTEST_BUILD) 
	cp qtest.ml $(QTEST_BUILD)/main.ml
	cd $(QTEST_BUILD) && \
	ocamlbuild -use-ocamlfind -tag 'package(qcheck)' main.native

qtest: $(QTEST_BUILD)/main.native
	./$(QTEST_BUILD)/main.native --verbose

clean:
	rm -rf $(QTEST_BUILD)
