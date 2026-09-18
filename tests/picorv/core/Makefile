# The full certified hierarchy is bit-level and deep. Icarus keeps this
# representative clocked integration regression reasonably quick; Verilator
# lint is a separate build gate.
SIM ?= icarus
TOPLEVEL_LANG := verilog
COCOTB_TOPLEVEL := PicoRV
COCOTB_TEST_MODULES := test_picorv
export PYTHONPATH := $(abspath ../..):$(PYTHONPATH)

include $(shell cocotb-config --makefiles)/Makefile.sim
