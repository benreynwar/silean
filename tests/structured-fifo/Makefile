SIM ?= verilator
TOPLEVEL_LANG := verilog
COCOTB_TOPLEVEL := structured_fifo
COCOTB_TEST_MODULES := test_fifo
export PYTHONPATH := $(abspath ..):$(PYTHONPATH)

include $(shell cocotb-config --makefiles)/Makefile.sim
