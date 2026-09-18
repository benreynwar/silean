SIM ?= verilator
TOPLEVEL_LANG := verilog
COCOTB_TOPLEVEL := register_bit
COCOTB_TEST_MODULES := test_register
export PYTHONPATH := $(abspath ../..):$(PYTHONPATH)

include $(shell cocotb-config --makefiles)/Makefile.sim
