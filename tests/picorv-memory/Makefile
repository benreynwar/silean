# The certified hierarchy is intentionally bit-level and deep. Icarus keeps
# this focused clocked protocol regression quick; Verilator lint is separate.
SIM ?= icarus
TOPLEVEL_LANG := verilog
COCOTB_TOPLEVEL := PicoRVMemory
COCOTB_TEST_MODULES := test_picorv_memory
export PYTHONPATH := $(abspath ..):$(PYTHONPATH)

include $(shell cocotb-config --makefiles)/Makefile.sim
