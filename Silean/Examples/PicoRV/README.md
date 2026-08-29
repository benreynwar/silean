# PicoRV32 port

This directory owns the PicoRV32-specific interfaces, behavioral
specifications, and the direct hardware port. It is an example
design rather than general-purpose Silean library machinery.

The first milestone defined and reviewed the exact configured ports and the
appropriate behavioral specification for every direct child:

- `PicoRV32Control` for sequencing;
- `PicoRV32Datapath` for registered execution values;
- `PicoRV32Memory`;
- `PicoRV32Decoder`;
- `PicoRV32Regs`.

`PicoRV32Alu` is a combinational child of `PicoRV32Datapath`, not a direct
top-level child.

Contract form follows the natural abstraction. In particular, the memory
specification includes temporal properties; it must not be limited to exact
cycle equations merely because `Contracts.Cycle.ModuleCycleContract` already
exists.

The source inventory places `reg_pc` and `reg_next_pc` in the datapath as well:
sequential, branch, and jump PC updates share the execution-result path and do
not form an independent source subsystem. The full decision and crossing-port
tables are in `docs/PicoRV32MainBlockInventory.md`.

Keep source names from `picorv32.v` in structural port maps. Lean-facing
interpretations may introduce clearer datatypes and projections without
renaming those hardware signals. General modules discovered while doing the
port belong in `Silean/Modules/`, not here.

The contract-only `PicoRV32Alu`, `PicoRV32Regs`, `PicoRV32Decoder`,
`PicoRV32Memory`, `PicoRV32Datapath`, and `PicoRV32Control` boundaries are
currently defined. The five direct-child contracts have been jointly reviewed
against the fixed Verilog configuration. The focused boundary check maps every
child input to a named producer and checks its signal type. `PicoRV.lean` now
builds that reviewed boundary as a typed `ModuleStructure`: its five children
remain explicit behavioral blackboxes, while the parent wiring and external
reset, memory, and trap ports are concrete.

The control contract preserves the configured fetch, operand, execute, shift,
load/store, trap, decoder-trigger, and memory-command sequencing. Its command
discipline correctly permits simultaneous prefetch and instruction-read during
promotion while excluding every overlap involving a data command, and is
linked directly to the memory contract's predicate.

The datapath contract preserves the configured source's registered PC,
operand, result, shift-count, and ALU-result flow. Its outputs have separate
rules for registered values, PC look-ahead, comparison, and writeback so that
the top level does not inherit false combinational dependencies.
Focused checks cover reset, sequential/JAL/JALR/branch PC flow, operand and ALU
capture, effective addresses, signed and unsigned loads, writeback, and
variable-latency iterative shifts.

The decoder contract
preserves the source's two registered decode stages and the extra cycle by
which its summary flags observe detailed instruction flags. The memory
contract preserves the single-outstanding external request state machine and
adds a natural request/transfer/completion view, including PicoRV32's delayed
prefetch completion. Neither is flattened into a simpler but cycle-inaccurate
function.
