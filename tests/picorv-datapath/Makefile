# The bit-level certified hierarchy is intentionally deep. Icarus keeps this
# clocked regression quick; the repository separately runs Verilator lint on
# the generated SystemVerilog.
SIM ?= icarus
TOPLEVEL_LANG := verilog
COCOTB_TOPLEVEL := picorv32_datapath
COCOTB_TEST_MODULES := test_picorv_datapath
export PYTHONPATH := $(abspath ..):$(PYTHONPATH)

include $(shell cocotb-config --makefiles)/Makefile.sim
