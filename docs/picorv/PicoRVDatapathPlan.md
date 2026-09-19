# PicoRV32 datapath implementation and proof plan

## Purpose and status

This document records the intended structure and proof argument for the
configured PicoRV32 datapath. The implementation now follows this plan: the
contract has focused executable examples, the complete standalone hierarchy
is closed, and a universal cycle certification connects the two.

The source of truth for the port is the sibling `picorv32/picorv32.v` checkout,
specialized to the configuration in [`PicoRV32Plan.md`](PicoRV32Plan.md). In
particular, this plan assumes 32-bit uncompressed instructions, dual-port
registers, a combinational ALU and comparison, the iterative two-stage shifter,
misalignment checking, and no counters, PCPI, IRQ, barrel shifter, trace, or
formal-only behavior.

The work has two deliverables:

1. a closed, universally certified standalone `PicoRVDatapath`; and
2. top-level migration of the closed Control, Datapath, and register-file
   children.

Both deliverables are complete. Memory and the two former Decoder behavioral
leaves have since been closed as well; `PicoRVTopChecks.lean` checks the
complete-core no-blackbox property directly.

Architectural correctness, reachable-state invariants, and retirement traces
are deliberately outside this plan.

## Source behavior and contract audit

The source has seven datapath-owned registers:

- `reg_pc` and `reg_next_pc` for current and prospective PCs;
- `reg_op1` and `reg_op2` for ALU operands and effective-address formation;
- `reg_out` for branch targets, completed shifts, and load results;
- `reg_sh` for the remaining iterative shift amount; and
- `alu_out_q` for the ALU result consumed by the following fetch/writeback
  cycle.

Four outputs expose current registered values. The other three are
combinational:

- `next_pc` selects aligned `reg_out` for a pending taken branch and otherwise
  exposes `reg_next_pc`;
- `alu_out_0` is the current certified ALU comparison; and
- `cpuregs_wrdata` selects the link, captured ALU result, or `reg_out` while in
  fetch.

The following table is the source-to-contract review checklist. “Matches”
means the existing natural function preserves source assignment priority and
pre-edge/nonblocking timing for defined two-state behavior.

| Source region | Configured behavior | Contract status |
| --- | --- | --- |
| combinational `next_pc` | taken branch uses `reg_out & ~1`; otherwise `reg_next_pc` | matches `nextPcFrom` |
| combinational ALU | priority comparison and result selection over current operands | matches the already certified `Alu` contract |
| combinational writeback | in fetch: branch link first, then ordinary stored result | matches `writebackFrom`; compressed `+2` and IRQ cases are absent |
| unconditional edge assignments | capture `alu_out` in `alu_out_q`; source assigns `x` to `reg_sh` and `reg_out` before phase overrides | ALU capture matches; retained `reg_sh`/`reg_out` are the chosen two-state totalization |
| reset | set only `reg_pc` and `reg_next_pc` to `PROGADDR_RESET = 0` after the unconditional assignments | matches `nextState` |
| fetch | choose branch result or `reg_next_pc`, copy it to both PC registers, then advance by four or the J immediate when decoding | matches `fetchNextState`, including use of pre-edge state |
| load RS1 | illegal instruction first; otherwise LUI/AUIPC/JAL, load, immediate shift, immediate ALU/JALR, then register operands | one correction required: add `instr_trap` and give it first priority |
| load RS2 | capture `cpuregs_rs2` into `reg_op2` and its low five bits into `reg_sh` | matches |
| execute | compute `reg_pc + decoded_imm` into `reg_out` regardless of branch/non-branch control updates | matches |
| shift | finish at zero; otherwise shift by four when the amount is at least four and by one otherwise | matches `shiftNextState`; selector overlap follows source case order |
| store | once prefetch permits progress, form the effective address only before the write command becomes active | matches `memoryNextState false` |
| load | form the effective address before the read command becomes active and capture formatted data only on final completion | matches `memoryNextState true` |

### Applied contract correction

`instr_trap` is a defined source condition, not an `x` value. In the source it
is the first `ld_rs1` case item. This matters for real illegal encodings: a
broad captured class such as the load opcode can be true even when no exact
instruction predicate recognizes its unsupported function bits. In that case
`instr_trap` is true and the source trap branch wins.

The current Datapath boundary omits `instr_trap`, so `loadRs1NextState` can
still capture operands for such an instruction. Control moves to trap and the
changed operands are not architecturally consumed, but that does not make the
standalone Datapath contract an exact cycle description.

The implementation applies the following correction:

1. add the source-named `instr_trap` input to `Datapath.ports` and `Inputs`;
2. map it from Decoder at the top-level boundary;
3. make `loadRs1NextState` retain its baseline when `instr_trap` is true;
4. update the rule dependency and fixtures; and
5. add a focused checked example where `instr_trap` overlaps a broad selector.

This is preferable to introducing a reachability premise into the standalone
certification. The hardware then implements the source priority for arbitrary
input combinations and the certification remains unconditional.

### Deliberate two-state totalizations

Lean signals contain Booleans, not Verilog's four-state values. The source uses
`x` for values that are irrelevant whenever consumed correctly. The contract
must nevertheless return a value on those paths:

- direct `x` defaults for `reg_sh`, `reg_out`, `reg_op1`, and `reg_op2` retain
  the corresponding pre-edge value unless a defined phase assignment wins;
- the existing ALU contract returns zero when no result class is selected, so
  unconditional `alu_out_q` capture is total;
- a completed load with no load-format latch returns zero; and
- writeback outside fetch, or fetch without a writeback latch, returns zero.

These choices are not claims about Verilog `x`. They make the structural
circuit total without adding validity hardware. Focused checks must cover all
defined selector cases and at least one no-selector totalization. Universal
certification proves the hardware follows these choices even for inconsistent
inputs.

## Proposed hierarchy

The outer sequential module should remain thin:

```text
PicoRVDatapath
|- storage       : aggregate Register DatapathState
|- stateFields   : named tuple splitter
|- alu           : existing certified PicoRV32Alu
|- next          : PicoRVDatapathNext
|- nextPc        : current next-PC output logic
|- writeback     : current writeback output logic
`- output wiring
```

One aggregate register is appropriate. The source owns these registers in one
synchronous process, and the contract computes every next-state field
together. It must be an ordinary register fed by reset-aware next-state logic:
reset changes only the PC registers and does not provide a uniform reset value
for the complete aggregate.

The ALU belongs beside `next`, rather than hidden inside it. Its current
comparison drives `alu_out_0`, while its word result is captured into
`alu_out_q` on every edge and is therefore also an input to next-state logic.
This makes the source's combinational-versus-registered timing visible in the
hierarchy.

The combinational next-state hierarchy should follow semantic source regions:

```text
PicoRVDatapathNext
|- baseline       : retain state and replace alu_out_q with current ALU result
|- phaseDecode    : full equality against each supported phase value
|- fetchUpdate    : current-PC selection and sequential/JAL PC arithmetic
|- loadRs1Update  : illegal-first operand-selection priority
|- loadRs2Update  : second register operand and shift-count capture
|- executeUpdate  : branch/effective target addition
|- shiftUpdate    : zero/four/one iterative step
|- memoryUpdate   : shared store/load effective-address and load-result logic
|- phase selection muxes
`- resetOverride  : zero only reg_pc and reg_next_pc
```

This is not a requirement to create a separate emitted module for every small
Lean helper. A child is warranted where it gives a named source region and a
useful semantic proof lemma. Simple selection and bit layouts should remain
generic instances inside those children.

### Reusable building blocks

The existing library is sufficient for the intended implementation:

- `Add 32` for PC and effective-address additions;
- `AddSub 5` or equivalent certified arithmetic for decrementing the shift
  amount;
- `VectorLayout` for clearing PC bit zero, taking the low five operand bits,
  fixed shifts by one or four, and sign-filling arithmetic right shifts;
- `EqualsConstant`, Boolean primitives, `Mux`, and named tuple adapters for
  selection and aggregate assembly;
- the certified PicoRV ALU; and
- the generic aggregate `Register` for storage.

A new generic variable shifter is not justified for this configured design:
the source uses only fixed one- and four-bit steps. If implementation reveals
a genuinely reusable missing primitive, its contract and certification must
be independent of PicoRV rather than hiding datapath behavior in
`Silean.Modules`.

## Natural correctness argument

The proof should be assembled in the same order as the circuit.

### 1. Establish local combinational meanings

Certify each semantic child independently. Its main theorem should state its
complete aggregate result in terms of the corresponding natural function:

- baseline output equals the old state with `alu_out_q` replaced;
- every phase comparator is exact over the full eight-bit value;
- each phase update equals its `DatapathContract.lean` helper;
- the phase mux chain equals `normalNextState`; and
- reset override equals `nextState` once supplied the selected normal state.

The phase decoder must not assume a one-hot or reachable phase. Likewise,
instruction selector muxes must preserve source priority for overlapping
inputs rather than assuming decoder mutual exclusion.

### 2. Certify `PicoRVDatapathNext`

Use the local child certifications to derive, for arbitrary inputs, current
state, and proposed child values:

```text
next.state = Datapath.nextState inputs current
```

This child has no contract state. Its proof therefore concerns only the
combinational aggregate equality and recursive no-blackbox closure.

### 3. Relate the aggregate register to contract state

For the stateful wrapper use the explicit correspondence:

```text
storage contract state .stored = stateMap.pack datapath contract state
```

State coverage follows by unpacking an arbitrary stored tuple. This is the
same shape as the successful Control proof, but the correspondence must be
stated locally rather than relying on definitional coincidence.

### 4. Prove current outputs

From the register observation and tuple splitter:

- `reg_pc`, `reg_op1`, `reg_op2`, and `reg_sh` equal the pre-edge contract
  state;
- the existing ALU certification gives `alu_out_0` from those same pre-edge
  operands;
- next-PC logic equals `nextPcFrom`; and
- writeback logic equals `writebackFrom`.

The output schedule exposes the inputs needed by each public output rule.
`comparison` inherits the ALU's deliberately bundled output rule, so its input
dependency is coarser than the Boolean result alone requires; this is safe for
the current parent schedule and avoids claiming a narrower dependency than the
certified ALU contract provides. Internal next-state logic reads the complete
input boundary.

### 5. Prove the edge transition

The ALU result and the current aggregate register feed the certified
`PicoRVDatapathNext`. Its output feeds the ordinary register input. Applying
the register state rule then establishes the correspondence for
`Datapath.nextState`. This proves the state rule without assuming anything
about phase encodings, selectors, memory latency, or reset history.

### 6. Prove closure

After bundling the universal cycle certification, prove
`moduleStructure.HasNoBlackboxes` recursively. Closed rendering is a separate
check: it catches naming collisions and missing emitted children that semantic
certification alone cannot detect.

## Focused checks

Executable examples teach the contract and protect the high-risk boundaries;
they do not replace universal certification.

The standalone check file should cover:

- reset zeros both PC registers while showing that ordinary outputs still
  expose pre-edge values;
- sequential fetch, JAL, JALR/taken-branch alignment, and untaken branch PC
  flow;
- LUI, immediate, first-register, and dual-register operand capture;
- illegal `ld_rs1` overlapping each broad selector class, demonstrating trap
  priority;
- unconditional ALU capture and the following fetch writeback;
- load/store effective-address formation before request activation;
- signed byte, signed halfword, and zero-extended load results;
- left, logical-right, and arithmetic-right iterative shifts;
- shift amounts zero, one, three, four, five, and thirty-one, including the
  four-then-one boundary and overlapping shift selectors;
- the defined no-selector totalizations;
- the universal certification and recursive no-blackbox witnesses; and
- successful closed FIRRTL rendering with stable root-module fragments.

Generated SystemVerilog should also receive a small clocked regression. At
minimum it must exercise reset, one PC transition, one ALU/writeback capture,
one load result, and a multi-cycle shift. Contract examples remain the more
exhaustive source of selector-priority coverage.

## Top-level migration (complete)

The completed migration followed this sequence:

1. replace the top-level Control blackbox with its existing certified
   structure;
2. replace the Datapath blackbox with the newly certified structure;
3. replace the register-file blackbox with its existing certified structure;
4. update the top-level internal verification's child contracts to use those
   certifications;
5. recheck complete output/state schedules and `HasAtMostOneSolution`;
6. render and lower the mixed hierarchy; and
7. audit the then-mixed recursive structure before the remaining Memory and
   Decoder leaves were subsequently closed.

Changing a child from its blackbox realization to a certified structure must
not change its public cycle contract. Therefore the existing top-level rule
schedule should remain valid modulo certification names. If it does not, that
is evidence of a boundary or dependency mistake and must be resolved rather
than papered over with a coarser schedule.

## Implementation order

1. Apply and check the `instr_trap` contract correction.
2. Implement and certify fixed bit layouts and arithmetic helpers needed by
   phase children, adding generic machinery only when necessary.
3. Implement the difficult shift and memory-update children first.
4. Implement fetch, operand capture, execute, baseline, phase decode, and
   reset override.
5. Assemble and universally certify `PicoRVDatapathNext`.
6. Build and universally certify the stateful wrapper.
7. Add focused contract, rendering, and clocked generated-hardware checks.
8. Migrate Control, Datapath, and register file at the top level and reprove
   the composition schedule.
9. Run the full Lean build, closed FIRRTL emission, CIRCT lowering, Verilator
   lint, and all generated-hardware regressions.
10. Audit the resulting blackbox inventory and update roadmap documentation.

## Completion criteria

This implementation is complete because all of the following are checked:

- the corrected Datapath contract agrees with every configured, defined
  source assignment and documents each `x` totalization;
- the standalone structure is universally certified against that contract;
- the complete standalone hierarchy has no blackboxes;
- focused examples cover every behavior listed above;
- closed FIRRTL renders, lowers, and passes Verilator lint;
- a clocked generated-hardware regression exercises representative stateful
  behavior;
- Control, Datapath, and register file are concrete top-level children;
- the top-level schedule and uniqueness proof still check;
- the remaining behavioral leaf inventory is exactly Memory and the two named
  Decoder children; and
- the full Lean and generated-hardware regression gates pass.
