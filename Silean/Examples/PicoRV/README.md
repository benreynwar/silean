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
`PicoRV32Datapath`, and `PicoRV32Control` boundaries are defined. `PicoRV32Regs`
and the combinational `PicoRV32Alu` have closed structural implementations.
`PicoRV32Decoder` has a certified two-stage parent structure whose capture and
resolve children remain explicit blackboxes; the other PicoRV blocks remain
contract-only. The five direct-child contracts have been jointly reviewed
against the fixed Verilog configuration. The focused boundary check maps every
child input to a named producer and checks its signal type. `PicoRV.lean` now
builds that reviewed boundary as a typed `ModuleStructure`: its five children
remain explicit behavioral blackboxes, while the parent wiring and external
reset, memory, and trap ports are concrete.

The standalone register-file structure preserves the original source port
names, wraps `RegisterBank (.vector 32 .bit) 5 2`, forces reads of `x0` to zero,
and suppresses writes to `x0` and writes while `resetn` is low. The top-level
still uses its specification blackbox until child migration is handled as a
separate step.

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
rules for registered values, PC look-ahead, comparison, and writeback so that
the top level does not inherit false combinational dependencies.
Focused checks cover reset, sequential/JAL/JALR/branch PC flow, operand and ALU
capture, effective addresses, signed and unsigned loads, writeback, and
variable-latency iterative shifts.

The decoder contract preserves the source's two registered decode stages and
the extra cycle by which its summary flags observe detailed instruction flags.
Its capture stage is a closed certified structure built from reusable slices,
comparisons, gates, adapters, and registers; the resolve stage remains an
explicit blackbox. The memory
contract preserves the single-outstanding external request state machine and
adds a natural request/transfer/completion view, including PicoRV32's delayed
prefetch completion. Neither is flattened into a simpler but cycle-inaccurate
function.
