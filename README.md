# Silean 2

Silean 2 describes typed hierarchical hardware in Lean, proves its structural
behavior against cycle contracts, and emits FIRRTL directly from the public
computable `ModuleStructure` hierarchy.

## Development environment

The checked-in Nix flake pins the complete development and simulation
toolchain: Elan/Lean, CIRCT `firtool`, Verilator, Make, Python, cocotb, and
pytest.

```sh
nix develop
```

The Lean version is then selected by `lean-toolchain`. No separate Python
virtual environment is required.

## Build and simulation

From inside `nix develop`:

```sh
make firrtl-bit-register   # build/bit-register/register_bit.fir
make verilog-bit-register # build/bit-register/register_bit.sv
make test-bit-register    # Verilator + cocotb
make test-structured-fifo # structured payload FIFO through Verilator + cocotb
```

`make`, `make all`, and `make test` run both verification pipelines. Generated
FIRRTL, SystemVerilog, and simulator objects live below `build/`, which is
ignored by Git. Cocotb result files and Python caches are also ignored.
`make clean` removes the two generated design directories below `build/`.

The cocotb test starts the standard cocotb `Clock` and uses a rising-edge then
falling-edge drive phase. It first establishes known register state without
assuming an initial value, then checks across several cycles that input changes
do not affect the output between rising edges and are captured at the next
rising edge.

The structured FIFO test carries a recursively named payload through the
generic FIFO, mux, logic, register, splitter, and combiner hierarchy. Its
generated ports retain field paths such as `input_data.b.d[1].f` in FIRRTL and
`input_data_b_d_1_f` in flattened SystemVerilog.

## Adding an emitted design

Each concrete hardware configuration gets a small Lean executable under
`Silean2/Emitters/`. Configuration remains ordinary typed Lean rather than a
command-line encoding. The executable passes its rendered circuit to the
shared `Silean2.FIRRTL.emitMain`, which writes to stdout or accepts
`--output PATH`.

Add a corresponding `lean_exe` entry to `lakefile.lean` and explicit Make
targets for its `.fir`, `.sv`, and simulation artifacts. Shared generation
logic belongs under `Silean2/FIRRTL/`; an emitter should contain only the
concrete design choice.
