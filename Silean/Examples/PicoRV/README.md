# PicoRV32 port

This directory owns the PicoRV32-specific boundaries, contracts, and hardware
port. It is an example design, not general-purpose Silean machinery. The
authoritative configuration, hierarchy, current status, and verification plan
are in [`docs/PicoRV32Plan.md`](../../../docs/PicoRV32Plan.md).

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

The source inventory places `reg_pc` and `reg_next_pc` in the datapath:
sequential, branch, and jump PC updates share the execution-result path and do
not form an independent source subsystem.

Keep source names from `picorv32.v` in structural port maps. Lean-facing
interpretations may introduce clearer datatypes and projections without
renaming those hardware signals. General modules discovered while doing the
port belong in `Silean/Modules/`, not here.

The `PicoRV32Alu`, `PicoRV32Regs`, `PicoRV32Decoder`, `PicoRV32Memory`,
`PicoRV32Datapath`, and `PicoRV32Control` boundaries all have universally
certified, recursively closed structural implementations. Control's aggregate
register wraps the concrete `ControlNext` hierarchy, whose decode, baseline,
all eight phase children, alignment/override, and command finishing are also
concrete and closed. The top-level hierarchy uses those five concrete direct
children, has no behavioral blackboxes, and has exactly one solution to its
simultaneous structural equations. Closed FIRRTL emission, CIRCT lowering,
Verilator lint, and representative clocked generated-hardware regressions
succeed for the complete core as well as the standalone stateful subsystems.
The five direct-child contracts have been jointly reviewed
against the fixed Verilog configuration. The focused boundary check maps every
child input to a named producer and checks its signal type. `PicoRV.lean`
builds that reviewed boundary as a typed mixed `ModuleStructure`, while the
parent wiring and external reset, memory, and trap ports are concrete.

The top-level register-file structure preserves the original source port
names, wraps `RegisterBank (.vector 32 .bit) 5 2`, forces reads of `x0` to zero,
and suppresses writes to `x0` and writes while `resetn` is low.

The ALU structure preserves all original source port names and contains one
shared `AddSub 32`, generic equality and bitwise modules, and generic muxes.
Unsigned comparison comes from subtraction no-borrow, while signed comparison
combines operand signs with that unsigned result. Public laws expose every
legal operation and the no-selection defaults without exposing the internal
instances. Its complete hierarchy is proven to contain no blackboxes. Shifts
remain in the iterative datapath, matching `BARREL_SHIFTER = 0`.

The control contract preserves the configured fetch, operand, execute, shift,
load/store, trap, decoder-trigger, and memory-command sequencing. Its command
discipline correctly permits simultaneous prefetch and instruction-read during
promotion while excluding every overlap involving a data command, and is
linked directly to the memory contract's predicate.

The datapath contract preserves the configured source's registered PC,
operand, result, shift-count, and ALU-result flow. Its outputs have separate
rules for registered values, PC look-ahead, comparison, and writeback. The
comparison rule intentionally inherits the certified ALU's bundled selector
dependency; the current parent schedule is compatible with that coarseness.
Focused checks cover reset, sequential/JAL/JALR/branch PC flow, operand and ALU
capture, effective addresses, signed and unsigned loads, writeback, and
variable-latency iterative shifts. Its reviewed structural and proof plan is
in [`docs/PicoRVDatapathPlan.md`](../../../docs/PicoRVDatapathPlan.md).

The decoder contract preserves the source's two registered decode stages and
the extra cycle by which its summary flags observe detailed instruction flags.
Its capture stage is a closed certified structure built from reusable slices,
comparisons, gates, adapters, and registers. Its resolve stage is also a
certified concrete structure. Immediate selection is a closed hierarchy of
vector layouts, gates, a constant, and priority muxes. Instruction matching
shares decoded fields across exact predicate gates; instruction summaries use
independent OR reductions, including the source's intentional omission of
ECALL/EBREAK from the recognized-instruction OR so it traps. The memory
contract preserves the single-outstanding external request state machine and
adds a natural request/transfer/completion view, including PicoRV32's delayed
prefetch completion. Neither stateful subsystem is flattened into a simpler
but cycle-inaccurate function.

The reviewed Memory source audit, proposed module hierarchy, natural proof
argument, and focused verification plan are in
[`docs/PicoRVMemoryPlan.md`](../../../docs/PicoRVMemoryPlan.md).
