RISCV_SIM ?= spike
XLEN ?= 64

src_dir ?= .
GDBSERVER_PY = $(src_dir)/gdbserver.py
TESTS = $(shell $(GDBSERVER_PY) --list-tests $(src_dir)/targets/RISC-V/spike32.py)
MULTI_TESTS = $(shell $(GDBSERVER_PY) --list-tests $(src_dir)/targets/RISC-V/spike32.py | \
	      grep -i multi)

default: spike$(XLEN) spike$(XLEN)-2

all-tests: spike32 spike-multi-limited spike32-2 spike32-2-hwthread \
	spike64 spike64-2 spike64-2-hwthread

slow-tests:	spike-multi all-tests

all:	pylint all-tests

run.%:
	$(GDBSERVER_PY) \
		$(src_dir)/targets/RISC-V/$(word 2, $(subst ., ,$@)).py \
		$(word 3, $(subst ., ,$@)) \
		--isolate \
		--print-failures \
		--sim_cmd $(RISCV)/bin/$(RISCV_SIM) \
		--server_cmd $(RISCV)/bin/openocd

# Target to check all the multicore options.
multi-tests: spike32-2 spike32-2-hwthread

pylint:
	pylint --rcfile=pylint.rc `git ls-files '*.py'`

spike-multi-limited:	$(foreach test, $(MULTI_TESTS), run.spike-multi.$(test))
	echo Finished $@

spike%:	$(foreach test, $(TESTS), run.spike%.$(test))
	echo Finished $@

clean:
	rm -f *.pyc
