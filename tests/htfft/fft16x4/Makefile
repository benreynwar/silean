SIM ?= icarus
TOPLEVEL_LANG := verilog
COCOTB_TOPLEVEL := htfft_16x4
COCOTB_TEST_MODULES := test_fft
COMPILE_ARGS += -DRANDOMIZE_REG_INIT
export PYTHONPATH := $(abspath ../..):$(PYTHONPATH)

include $(shell cocotb-config --makefiles)/Makefile.sim
