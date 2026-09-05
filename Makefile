BUILD_DIR := build
BIT_REGISTER_DIR := $(BUILD_DIR)/bit-register
BIT_REGISTER_FIRRTL := $(BIT_REGISTER_DIR)/register_bit.fir
BIT_REGISTER_VERILOG := $(BIT_REGISTER_DIR)/register_bit.sv
BIT_REGISTER_SIM := $(BIT_REGISTER_DIR)/sim
STRUCTURED_FIFO_DIR := $(BUILD_DIR)/structured-fifo
STRUCTURED_FIFO_FIRRTL := $(STRUCTURED_FIFO_DIR)/one_entry_fifo.fir
STRUCTURED_FIFO_VERILOG := $(STRUCTURED_FIFO_DIR)/one_entry_fifo.sv
STRUCTURED_FIFO_SIM := $(STRUCTURED_FIFO_DIR)/sim
SERIAL_FIFO_DIR := $(BUILD_DIR)/serial-fifo
SERIAL_FIFO_FIRRTL := $(SERIAL_FIFO_DIR)/serial_fifo.fir
SERIAL_FIFO_VERILOG := $(SERIAL_FIFO_DIR)/serial_fifo.sv
SERIAL_FIFO_SIM := $(SERIAL_FIFO_DIR)/sim
REGISTER_BANK_DIR := $(BUILD_DIR)/register-bank
REGISTER_BANK_FIRRTL := $(REGISTER_BANK_DIR)/bit_register_bank.fir
REGISTER_BANK_VERILOG := $(REGISTER_BANK_DIR)/bit_register_bank.sv
REGISTER_BANK_SIM := $(REGISTER_BANK_DIR)/sim
POINTER_FIFO_DIR := $(BUILD_DIR)/pointer-fifo
POINTER_FIFO_FIRRTL := $(POINTER_FIFO_DIR)/pointer_fifo.fir
POINTER_FIFO_VERILOG := $(POINTER_FIFO_DIR)/pointer_fifo.sv
POINTER_FIFO_SIM := $(POINTER_FIFO_DIR)/sim

LEAN_SOURCES := $(shell find Silean -type f -name '*.lean')
LEAN_BUILD_INPUTS := $(LEAN_SOURCES) lakefile.lean lean-toolchain lake-manifest.json
CHECK_SOURCES := $(shell find Silean/Examples/Checks -type f -name '*Checks.lean' | sort)

.PHONY: all check-example-imports firrtl-bit-register verilog-bit-register test-bit-register \
	firrtl-structured-fifo verilog-structured-fifo test-structured-fifo test clean \
	firrtl-register-bank verilog-register-bank test-register-bank \
	firrtl-pointer-fifo verilog-pointer-fifo test-pointer-fifo \
	firrtl-serial-fifo verilog-serial-fifo test-serial-fifo

all: test

firrtl-bit-register: $(BIT_REGISTER_FIRRTL)

verilog-bit-register: $(BIT_REGISTER_VERILOG)

test: check-example-imports test-bit-register test-structured-fifo test-serial-fifo \
	test-register-bank test-pointer-fifo

check-example-imports:
	@status=0; \
	for file in $(CHECK_SOURCES); do \
		module=$$(printf '%s' "$$file" | sed 's#/#.#g; s#\.lean$$##'); \
		if ! grep -Fqx "import $$module" SileanExamples.lean; then \
			echo "SileanExamples.lean does not import $$module"; \
			status=1; \
		fi; \
	done; \
	exit $$status

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

firrtl-serial-fifo: $(SERIAL_FIFO_FIRRTL)

verilog-serial-fifo: $(SERIAL_FIFO_VERILOG)

test-serial-fifo: $(SERIAL_FIFO_VERILOG)
	$(MAKE) --no-print-directory -C tests/serial-fifo \
		VERILOG_SOURCES=$(abspath $(SERIAL_FIFO_VERILOG)) \
		SIM_BUILD=$(abspath $(SERIAL_FIFO_SIM))

firrtl-register-bank: $(REGISTER_BANK_FIRRTL)

verilog-register-bank: $(REGISTER_BANK_VERILOG)

test-register-bank: $(REGISTER_BANK_VERILOG)
	$(MAKE) --no-print-directory -C tests/register-bank \
		VERILOG_SOURCES=$(abspath $(REGISTER_BANK_VERILOG)) \
		SIM_BUILD=$(abspath $(REGISTER_BANK_SIM))

firrtl-pointer-fifo: $(POINTER_FIFO_FIRRTL)

verilog-pointer-fifo: $(POINTER_FIFO_VERILOG)

test-pointer-fifo: $(POINTER_FIFO_VERILOG)
	$(MAKE) --no-print-directory -C tests/pointer-fifo \
		VERILOG_SOURCES=$(abspath $(POINTER_FIFO_VERILOG)) \
		SIM_BUILD=$(abspath $(POINTER_FIFO_SIM))

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

$(SERIAL_FIFO_FIRRTL): $(LEAN_BUILD_INPUTS)
	mkdir -p $(@D)
	lake exe emit-serial-fifo --output $@

$(SERIAL_FIFO_VERILOG): $(SERIAL_FIFO_FIRRTL)
	firtool --format=fir $< -o $@

$(REGISTER_BANK_FIRRTL): $(LEAN_BUILD_INPUTS)
	mkdir -p $(@D)
	lake exe emit-bit-register-bank --output $@

$(REGISTER_BANK_VERILOG): $(REGISTER_BANK_FIRRTL)
	firtool --format=fir $< -o $@

$(POINTER_FIFO_FIRRTL): $(LEAN_BUILD_INPUTS)
	mkdir -p $(@D)
	lake exe emit-pointer-fifo --output $@

$(POINTER_FIFO_VERILOG): $(POINTER_FIFO_FIRRTL)
	firtool --format=fir $< -o $@

clean:
	rm -rf $(BIT_REGISTER_DIR) $(STRUCTURED_FIFO_DIR) $(REGISTER_BANK_DIR) \
		$(POINTER_FIFO_DIR) $(SERIAL_FIFO_DIR)
