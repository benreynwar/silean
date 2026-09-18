SIM ?= verilator
TOPLEVEL_LANG := verilog
COCOTB_TOPLEVEL := bit_register_bank
COCOTB_TEST_MODULES := test_register_bank
export PYTHONPATH := $(abspath ../..):$(PYTHONPATH)

include $(shell cocotb-config --makefiles)/Makefile.sim
