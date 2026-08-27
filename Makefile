BUILD_DIR := build
BIT_REGISTER_DIR := $(BUILD_DIR)/bit-register
BIT_REGISTER_FIRRTL := $(BIT_REGISTER_DIR)/register_bit.fir
BIT_REGISTER_VERILOG := $(BIT_REGISTER_DIR)/register_bit.sv
BIT_REGISTER_SIM := $(BIT_REGISTER_DIR)/sim
STRUCTURED_FIFO_DIR := $(BUILD_DIR)/structured-fifo
STRUCTURED_FIFO_FIRRTL := $(STRUCTURED_FIFO_DIR)/one_entry_fifo.fir
STRUCTURED_FIFO_VERILOG := $(STRUCTURED_FIFO_DIR)/one_entry_fifo.sv
STRUCTURED_FIFO_SIM := $(STRUCTURED_FIFO_DIR)/sim
REGISTER_BANK_DIR := $(BUILD_DIR)/register-bank
REGISTER_BANK_FIRRTL := $(REGISTER_BANK_DIR)/bit_register_bank.fir
REGISTER_BANK_VERILOG := $(REGISTER_BANK_DIR)/bit_register_bank.sv
REGISTER_BANK_SIM := $(REGISTER_BANK_DIR)/sim

LEAN_SOURCES := $(shell find Silean2 -type f -name '*.lean')
LEAN_BUILD_INPUTS := $(LEAN_SOURCES) lakefile.lean lean-toolchain lake-manifest.json

.PHONY: all firrtl-bit-register verilog-bit-register test-bit-register \
	firrtl-structured-fifo verilog-structured-fifo test-structured-fifo test clean \
	firrtl-register-bank verilog-register-bank test-register-bank

all: test

firrtl-bit-register: $(BIT_REGISTER_FIRRTL)

verilog-bit-register: $(BIT_REGISTER_VERILOG)

test: test-bit-register test-structured-fifo test-register-bank

test-bit-register: $(BIT_REGISTER_VERILOG)
	$(MAKE) --no-print-directory -C tests/bit-register \
		VERILOG_SOURCES=$(abspath $(BIT_REGISTER_VERILOG)) \
		SIM_BUILD=$(abspath $(BIT_REGISTER_SIM))

firrtl-structured-fifo: $(STRUCTURED_FIFO_FIRRTL)

verilog-structured-fifo: $(STRUCTURED_FIFO_VERILOG)

test-structured-fifo: $(STRUCTURED_FIFO_VERILOG)
	$(MAKE) --no-print-directory -C tests/structured-fifo \
		VERILOG_SOURCES=$(abspath $(STRUCTURED_FIFO_VERILOG)) \
		SIM_BUILD=$(abspath $(STRUCTURED_FIFO_SIM))

firrtl-register-bank: $(REGISTER_BANK_FIRRTL)

verilog-register-bank: $(REGISTER_BANK_VERILOG)

test-register-bank: $(REGISTER_BANK_VERILOG)
	$(MAKE) --no-print-directory -C tests/register-bank \
		VERILOG_SOURCES=$(abspath $(REGISTER_BANK_VERILOG)) \
		SIM_BUILD=$(abspath $(REGISTER_BANK_SIM))

$(BIT_REGISTER_FIRRTL): $(LEAN_BUILD_INPUTS)
	mkdir -p $(@D)
	lake exe emit-bit-register --output $@

$(BIT_REGISTER_VERILOG): $(BIT_REGISTER_FIRRTL)
	firtool --format=fir $< -o $@

$(STRUCTURED_FIFO_FIRRTL): $(LEAN_BUILD_INPUTS)
	mkdir -p $(@D)
	lake exe emit-structured-fifo --output $@

$(STRUCTURED_FIFO_VERILOG): $(STRUCTURED_FIFO_FIRRTL)
	firtool --format=fir $< -o $@

$(REGISTER_BANK_FIRRTL): $(LEAN_BUILD_INPUTS)
	mkdir -p $(@D)
	lake exe emit-bit-register-bank --output $@

$(REGISTER_BANK_VERILOG): $(REGISTER_BANK_FIRRTL)
	firtool --format=fir $< -o $@

clean:
	rm -rf $(BIT_REGISTER_DIR) $(STRUCTURED_FIFO_DIR) $(REGISTER_BANK_DIR)
