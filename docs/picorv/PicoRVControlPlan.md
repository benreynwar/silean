# PicoRV32 control implementation and proof plan

## Purpose and status

This document describes how to turn the existing `PicoRV.Control` cycle
contract into concrete, certified hardware. It is deliberately written before
the hardware structure. The immediate objective is to agree on the semantic
decomposition, proof argument, and module hierarchy before committing to a
large network of registers, comparisons, gates, and muxes.

The Verilog cross-check below was used to freeze the cycle contract before
structural work. Its `ld_rs2` discrepancy has been corrected. The standalone
registered Control structure and its combinational `ControlNext` hierarchy are
now universally certified against `Control.cycleContract` and
`Control.nextState`. Phase decode, baseline, alignment, reset/alignment
override, command finish, and all eight phase children are concrete and
closed. Closed FIRRTL emission and CIRCT lowering succeed. The certified
Control structure is now integrated into the recursively closed top-level
PicoRV hierarchy. Separate reachability and trace invariants remain future
work.

This plan has three priorities:

1. preserve the configured `picorv32.v` cycle behavior, including assignment
   order and nonblocking timing;
2. give the structural proof semantic intermediate statements instead of one
   monolithic gate-level simplification; and
3. keep PicoRV-specific sequencing out of the reusable `Silean.Modules`
   namespace.

## What the existing contract says

Control owns sixteen source-level registers:

- the eight-bit `cpu_state` phase;
- `latched_store`, `latched_stalu`, and `latched_branch`;
- the load-format flags `latched_is_lu`, `latched_is_lh`, and `latched_is_lb`;
- the five-bit destination `latched_rd`;
- the two-bit `mem_wordsize`;
- the four memory commands `mem_do_prefetch`, `mem_do_rinst`,
  `mem_do_rdata`, and `mem_do_wdata`;
- `decoder_trigger` and `decoder_pseudo_trigger`; and
- the registered `trap` output.

All outputs except `cpuregs_write` expose current values of those registers.
`cpuregs_write` is combinational: it is true in the fetch phase when either
`latched_branch` or `latched_store` is true.

The next-state function has four semantic layers. Their order is part of the
contract:

1. **Baseline assignments.** Clear `trap` and `decoder_pseudo_trigger`, and
   set `decoder_trigger` from the current instruction-read command and
   `mem_done`. Every other field initially retains its current value.
2. **Reset or phase transition.** Reset selects the reset transition.
   Otherwise exactly one recognized `cpu_state` value selects its phase
   transition. An unrecognized state retains the baseline.
3. **Misalignment override.** While reset is inactive, a current data or
   instruction request with a misaligned address forces the next phase to
   trap. It changes only `cpu_state`; other decisions already made by the
   selected phase remain in force.
4. **Command completion.** Reset or `mem_done` first clears all four memory
   commands. The phase transition's `setRinst`, `setRdata`, and `setWdata`
   intents are then applied, so a command may be reasserted on the same edge.
   There is intentionally no corresponding `setPrefetch` intent.

The `Transition` record in `Control.lean` is not incidental proof machinery.
It records the source distinction between ordinary nonblocking state updates
and the three blocking `set_mem_do_*` temporaries. It should remain the
semantic interface used to explain the hardware.

## Phase behavior in plain language

The phase encodings are eight distinct one-hot constants, but the contract is
total over every eight-bit value. Hardware must compare the complete value
against each constant; it must not use an individual state bit while assuming
the state is one-hot.

### Trap

The trap phase stays in the trap phase and sets the registered `trap` output.
The next cycle's baseline clears `trap` before the phase sets it again.

### Fetch

Fetch initializes instruction-read bookkeeping and clears the transient
writeback/load-format latches. It captures `decoded_rd` every cycle.

If the current `decoder_trigger` is false, fetch requests an instruction and
otherwise remains in fetch. If it is true, fetch consumes the decoded
instruction. JAL stays in fetch, starts another instruction read, and records
a branch writeback. Every other instruction moves to `ld_rs1`; prefetch is
enabled except for JALR.

The decision reads the current `decoder_trigger`, not the baseline value being
computed for the next edge.

### Load operand one

The first-operand phase uses an explicit priority order:

1. illegal instruction enters trap;
2. LUI/AUIPC/JAL enters execute and may promote prefetch to instruction read;
3. loads enter `ldmem` and request the next instruction;
4. immediate shifts enter shift;
5. JALR and ordinary immediate ALU operations enter execute and may promote
   prefetch;
6. stores enter `stmem` and request the next instruction;
7. register shifts enter shift; and
8. everything else enters execute and may promote prefetch.

The decoder inputs are not assumed mutually exclusive for certification. The
hardware must preserve this order for inconsistent inputs as well as for
reachable executions.

### Load operand two

The second-operand phase has a shorter priority chain: store, register shift,
then ordinary execute. There is no illegal-instruction branch because PCPI is
disabled. The phase must remain a separate contract from the first-operand
phase even though some suffixes are similar.

### Execute

A branch-class instruction clears the destination register, records the ALU
comparison in both `latched_store` and `latched_branch`, returns to fetch when
`mem_done` is true, suppresses a simultaneously produced decoder trigger for
a taken branch, and raises the `setRinst` intent for a taken branch.

A non-branch instruction records an ordinary writeback, records whether it is
JALR, marks the result as an ALU result, and returns to fetch.

### Shift

Shift always marks a pending register write. A zero current shift amount
returns to fetch and may promote prefetch to instruction read. A nonzero amount
remains in the shift phase. The zero test is over the complete five-bit value.

### Store memory

While a prefetch is active and has not completed, the store phase waits and
makes no store request. Otherwise, the first store cycle captures byte, half,
or word size and raises `setWdata`. Completion without a current prefetch
returns to fetch and raises both decoder trigger signals.

### Load memory

Load has the same prefetch wait condition. Its first request cycle captures
the load size and signedness flags and raises `setRdata`. Completion without a
current prefetch returns to fetch and raises both decoder trigger signals.

The load and store handshakes are similar, but their captured metadata differs.
We should prove them separately before considering any generalized reusable
memory-phase component.

## Verilog cross-check

This plan was checked against the clean sibling `picorv32` checkout at commit
`a473fc8fca393771d83b0ffcf0b14db3393339d8`, specifically
`picorv32.v`. The comparison applies the fixed parameters in
`PicoRV32Plan.md`: counters, PCPI, multiply/divide, IRQ, trace, compressed ISA,
barrel shift, and two-cycle ALU/compare are disabled; dual-port registers,
misalignment trapping, and illegal-instruction trapping are enabled; and
`STACKADDR` is all ones.

The source's main sequential block mixes control and datapath assignments.
This audit compares only the registers owned by `PicoRV.Control`; the omitted
PC, operand, result, and shift updates are obligations of the Datapath
contract.

| Source region | Configured behavior | Lean contract status |
| --- | --- | --- |
| `cpuregs_write`, lines 1309–1334 | In fetch, write for a pending branch or ordinary store; IRQ cases disappear | Matches `cpuregsWrite` |
| Main-block defaults, lines 1402–1450 | Clear blocking command intents, clear trap and pseudo-trigger, derive decoder trigger from current instruction completion | Matches the baseline and `Transition` intents |
| Reset, lines 1457–1484 | Clear the six latch flags and phase to fetch; the disabled stack initialization disappears | Matches `resetTransition`; commands are cleared later |
| Fetch, lines 1491–1576 | Clear transient latches, capture destination, wait/request when undecoded, then choose JAL or load-RS1 | Matches after configuration reduction, subject to `do_waitirq` below |
| Load RS1, lines 1579–1757 | Illegal trap, direct/immediate classes, load, shift, store, or default execute in source case order | Matches `loadRs1Transition` after disabled branches are removed |
| Load RS2, lines 1759–1803 | With PCPI disabled, only store, register shift, and default execute remain | Matches `loadRs2Transition` |
| Execute, lines 1805–1827 | Branch captures comparison and may reissue instruction read; non-branch records ALU writeback and returns to fetch | Matches `executeTransition` |
| Shift, lines 1829–1852 | Mark writeback; return to fetch and promote prefetch only when the current shift count is zero | Control-owned portion matches `shiftTransition` |
| Store, lines 1854–1878 | Wait for prefetch, capture size and set write intent on start, trigger decode and fetch on completion | Matches `storeTransition`, with deterministic invalid-selector totalization |
| Load, lines 1880–1912 | Wait for prefetch, capture size/sign flags and set read intent on start, trigger decode and fetch on completion | Matches `loadTransition`, with deterministic invalid-selector totalization |
| Misalignment, lines 1922–1947 | Current data/instruction commands and low address bits can override the selected next phase with trap | Matches `dataMisaligned`, `instructionMisaligned`, and their late override |
| Command finish, lines 1949–1961 | Reset/completion clears all commands, then blocking intent flags reassert read/write commands | Matches `finishCommands` and its ordering |

### Resolved finding: `ld_rs2` illegal-instruction behavior

The source guards its `cpu_state_ld_rs2` illegal-instruction branch with
`WITH_PCPI && instr_trap`. All contributors to `WITH_PCPI` are disabled in the
fixed configuration, so that branch is absent. The Lean
`loadRs2Transition` originally tested `instr_trap` unconditionally and entered
the trap phase.

`cpu_state_ld_rs2` is unreachable after reset when dual-port registers are
enabled, so this does not change configured reachable execution. It does
matter to the total cycle function on arbitrary states, and the proposed
certification explicitly covers arbitrary states. The branch has therefore
been removed from the contract, and a focused check records that `instr_trap`
does not alter an arbitrary `ld_rs2` state in this configuration.

### Finding 2: eliminated `do_waitirq` state

The Verilog fetch request is gated by `!decoder_trigger && !do_waitirq`.
`do_waitirq` is unconditionally cleared each edge and can be set only inside
an IRQ-enabled branch. With IRQ disabled it is always false after the first
edge, but as an unreset Verilog register its pre-edge value is not constrained
before then. The Lean specialization omits this disabled-feature state and
uses only `!decoder_trigger`.

The recommended policy is to keep `do_waitirq` out of the configured Control
boundary and state explicitly that this is reset-synchronized configuration
specialization, not equivalence for an arbitrary pre-reset Verilog register
valuation. Adding an otherwise dead register merely to model the first
pre-reset edge would make the natural configured contract worse. This policy
must be consistent with the eventual whole-core reset theorem.

### Finding 3: deterministic totalization of source don't-cares

Several source cases carry `parallel_case`/`full_case` annotations and rely on
reachable decoder invariants. The Lean contract assigns deterministic priority
when selectors overlap and deterministic word size zero when no store/load
size selector matches. This is a reasonable two-state totalization, but it is
stronger than the source's intended behavior outside its legal environment.

We should retain these deterministic choices because they make the natural
cycle contract total and implementable. Later reachability proofs must show
that legal execution stays within the source's intended selector conditions;
cycle certification must still implement the chosen totalization for every
input.

## Adopted audit decisions

The Verilog comparison produced three decisions, now adopted as follows:

1. the unconditional `instr_trap` case was removed from `loadRs2Transition`,
   because it is not present when `WITH_PCPI` is false;
2. explicitly define equivalence as beginning from reset-synchronized states,
   so the disabled IRQ-only `do_waitirq` register remains outside the Control
   contract; and
3. retain Lean's deterministic priority and default values outside the
   Verilog decoder's legal environment, while proving separately that reachable
   decoder outputs satisfy that environment.

Only the first item required a change to `Control.lean`. None of these decisions
changes the enabled, reset-reachable behavior of the configured core.

## Remaining contract audit before structural work

The structure will certify against the Lean contract, so a contract error
would be faithfully implemented rather than discovered by certification. The
cross-check above covers the phase and global priority structure. This
assignment matrix records every source assignment to a Control-owned register
after disabled configuration branches are removed. "Retain" means that the
Verilog makes no assignment at that point and the register keeps its pre-edge
value.

| Register | Default/reset assignments | Phase assignments | Later overriding assignments |
| --- | --- | --- | --- |
| `cpu_state` | reset: fetch | trap retains; fetch: retain or `ld_rs1`; `ld_rs1`: trap/load/shift/store/execute; `ld_rs2`: store/shift/execute; execute non-branch: fetch; execute branch with `mem_done`: fetch; shift with zero count: fetch; completed load/store: fetch | active misalignment: trap |
| `latched_store` | reset and fetch: false | execute branch: `alu_out_0`; execute non-branch, shift, and load: true | none |
| `latched_stalu` | reset and fetch: false | execute non-branch: true | none |
| `latched_branch` | reset and fetch: false | decoded JAL: true; execute branch: `alu_out_0`; execute non-branch: `instr_jalr` | none |
| `latched_is_lu` | reset and fetch: false | starting load: `is_lbu_lhu_lw` | none |
| `latched_is_lh` | reset and fetch: false | starting load: `instr_lh` | none |
| `latched_is_lb` | reset and fetch: false | starting load: `instr_lb` | none |
| `latched_rd` | reset: retain because `STACKADDR` is all ones; fetch: `decoded_rd` | execute branch: zero | none |
| `mem_wordsize` | reset: retain; fetch: zero | starting store/load: selected size | none |
| `mem_do_prefetch` | reset: retain in reset block | decoded non-JAL fetch: `!instr_jalr` | reset or `mem_done`: false |
| `mem_do_rinst` | reset: retain in reset block | fetch: `!decoder_trigger`, then JAL: true or decoded non-JAL: false; `ld_rs1`: true for load/store or current prefetch for execute paths; `ld_rs2`: true for store or current prefetch for execute; zero-count shift: current prefetch; taken branch raises `setRinst` | reset or `mem_done`: false, then `setRinst`: true |
| `mem_do_rdata` | reset: retain in reset block | starting load raises `setRdata` | reset or `mem_done`: false, then `setRdata`: true |
| `mem_do_wdata` | reset: retain in reset block | starting store raises `setWdata` | reset or `mem_done`: false, then `setWdata`: true |
| `decoder_trigger` | every edge: current `mem_do_rinst && mem_done`; reset does not replace it | taken branch: false; completed load/store: true | none |
| `decoder_pseudo_trigger` | every edge: false; reset does not replace it | completed load/store: true | none |
| `trap` | every edge: false; reset does not replace it | trap phase: true | none |

This matrix agrees with `Control.nextState`. In particular,
the seemingly surprising reset retention of `latched_rd`, `mem_wordsize`, and
the command fields before the common clear is intentional, as are the baseline
values of the two decoder triggers and `trap`. The final command-clear layer
means all four commands are nevertheless false after a reset edge.

The source-to-contract review is closed for the configured Control-owned
registers. During implementation, each row above should become a focused
correspondence lemma or be covered by the enclosing transition lemma; the
matrix is the checklist for ensuring that no source assignment disappears
inside a broad helper.

Particular audit risks are:

- command clearing followed by same-cycle command reassertion;
- `decoder_trigger` being derived before reset/phase handling;
- reset clearing only the fields named by `resetTransition`, rather than every
  control register;
- misalignment overriding only the phase after the phase transition;
- taken-branch interaction among `mem_done`, `decoder_trigger`, and
  `setRinst`;
- prefetch promotion allowing `mem_do_prefetch` and `mem_do_rinst` together;
- the distinct selector priorities in `ld_rs1` and `ld_rs2`; and
- the configured-away `ld_rs2` illegal-instruction branch, now covered by a
  focused contract check.

The focused `PicoRVControlNextChecks` examples now cover the high-risk
priority boundaries above, including arbitrary unknown phases. They are
regression witnesses alongside—rather than substitutes for—the universal
cycle certifications.

## Proposed module hierarchy

A hierarchy is warranted. A flat control module would contain enough child
instances and enough interacting rewrite facts that its certification would
become difficult to review. The hierarchy should follow semantic proof
boundaries, not create a hardware module for every Lean helper function.

The proposed outer structure is:

```text
PicoRVControl
|- state register       : one named aggregate ControlState register
|- state splitter       : exposes current source-named fields
|- next                 : PicoRVControlNext combinational hierarchy
|- writeback predicate  : exact fetch comparison plus Boolean gates
`- output wiring
```

`PicoRVControl` should be a thin sequential wrapper. `ControlState` should be
a named tuple with the same field names and signal types as the contract state.
One aggregate register is appropriate because the source uses one synchronous
control process and the contract supplies a total next value for every field.
The generic register hierarchy still produces concrete storage for every bit.
It must be an ordinary register fed by reset-aware next-state logic, not a
uniform reset register: reset is synchronous and deliberately leaves some
fields unchanged. Schema-aware naming must preserve readable emitted field
names.

The proposed combinational hierarchy is:

```text
PicoRVControlNext
|- phaseDecode       : exact equality with all eight phase constants
|- baseline          : trap/trigger defaults over retained current state
|- trapTransition
|- fetchTransition
|- loadRs1Transition
|- loadRs2Transition
|- executeTransition
|- shiftTransition
|- storeTransition
|- loadTransition
|- phase selection   : priority muxes over the Transition tuple
|- alignment         : data and instruction misalignment predicates
|- reset/override    : reset choice, then misalignment phase replacement
`- commandFinish     : clear commands, then apply set-command intents
```

The phase-transition children are PicoRV-private modules. Each receives the
current state, the baseline state, and only the external inputs its contract
uses. Each produces the natural `Transition` tuple: a complete proposed state
plus `setRinst`, `setRdata`, and `setWdata`.

Producing a complete transition from each phase makes phase selection an
ordinary typed mux over one aggregate value. This is wider than hand-sharing
every individual mux, but it mirrors the source `case` statement, gives each
child a natural contract, and lets synthesis remove redundant paths. We should
only abandon this representation if emitted FIRRTL becomes unreasonable or
the proof reveals a genuine mismatch.

`alignment` and `commandFinish` deserve named private modules because they are
global priority layers applied after phase selection. Folding either into all
phase children would duplicate logic and obscure the source assignment order.

`phaseDecode` also deserves a named module. It must use full-value equality
rather than relying on a reachability invariant. Its outputs are mutually
exclusive because the eight constants are distinct, a theorem that will make
the phase-selection proof straightforward.

We should not initially create a reusable generic state-machine framework.
The phase transition shapes, blocking command intents, and priority layers are
specific to this PicoRV source. Reusable components should be extracted only
when a second concrete use demonstrates a stable abstraction.

## Arithmetic and Boolean bridge lemmas

Several readable arithmetic predicates in the contract need small proofs that
they equal simpler hardware tests:

- `phase state = constant` equals equality of the eight-bit state vector with
  that constant;
- `shiftAmount inputs = 0` equals equality of the five shift bits with zero;
- `wordSize state = 0` and `wordSize state = 1` equal two-bit constant
  comparisons;
- `toNat reg_op1 % 4 ≠ 0` equals `reg_op1[0] || reg_op1[1]`;
- `toNat reg_pc % 4 ≠ 0` equals `reg_pc[0] || reg_pc[1]`; and
- the halfword misalignment test is exactly `reg_op1[0]`.

These lemmas should be proved before assembling `PicoRVControlNext`. They are
the semantic bridge between the natural contract and the intended slices,
equality modules, and gates. They should live with the Control specification
unless they become genuinely general bit-vector facts.

## Natural-language correctness proof

The intended top-level theorem is that the concrete `PicoRVControl` structure
implements the existing `Control.cycleContract`. The argument is as follows.

Let the structural state be the state of the aggregate register. Relate it to
a contract state exactly when unpacking the register value yields every
contract register value. This relation is total in both directions and does
not assume that `cpu_state`, command bits, or decoder inputs are well formed.

At the start of a cycle, the register's observation rule produces its current
aggregate value. The splitter therefore exposes exactly the related contract
state. Every ordinary state output is wired from the corresponding split
field, so those outputs equal `outputValues`. The writeback comparison proves
that its phase flag is true exactly when `phase state = cpuStateFetch`; the OR
and AND gates therefore produce exactly `cpuregsWrite state`.

For next state, first use the baseline child's contract to show that its output
equals the contract state with precisely the three baseline assignments. For
each phase child, prove extensionally over the `Transition` fields that its
output equals the corresponding pure transition function. These proofs may
split on the child's ordered Boolean selectors, but they must not assume those
selectors are mutually exclusive.

The phase decoder compares the complete current state against distinct
constants. Consequently at most one phase flag is true. A mux chain ordered
trap, fetch, load-RS1, load-RS2, execute, shift, store, and load therefore
selects the same transition as `phaseTransition`; if no equality holds, it
selects the unchanged baseline transition.

Next, the reset selector chooses `resetTransition baseline` exactly when
`!resetn`. The alignment bridge lemmas show that the structural alignment
network equals `dataMisaligned || instructionMisaligned`. The following mux
forces only the selected transition's `cpu_state` field to the trap constant
exactly when reset is inactive and that predicate is true. Thus the structural
result after this mux equals the contract's second transition override.

Finally, the command-finishing child clears all commands exactly when
`!resetn || mem_done`, and then applies the three intent bits in source order.
Its output is therefore `finishCommands` of the selected transition. Combining
the preceding equalities gives the central combinational lemma:

```text
ControlNext.output inputs current = Control.nextState inputs current
```

The aggregate register captures that value on the edge. Unpacking its next
structural state therefore yields the contract's next state, re-establishing
the state relation. Certified children and a valid rule schedule supply a
structural result for every input and structural state and prove it unique.
This establishes the cycle implementation theorem without any reachability
assumption. Recursive closure of the register, adapters, comparisons, gates,
muxes, and all private combinational children then proves
`PicoRVControl.moduleStructure.HasNoBlackboxes`.

## Formal proof decomposition

The Lean proof should expose the following intermediate results rather than
letting a large `simp` call define the argument:

1. pack/unpack laws between `ControlState` and `stateMap.Values`;
2. exact phase-comparison and mutual-exclusion laws;
3. one correctness theorem for every phase-transition child;
4. `phaseSelection_eq_phaseTransition`;
5. the alignment arithmetic bridge lemmas;
6. `resetAndAlignment_eq_transitionOverrides`;
7. `commandFinish_eq_finishCommands`;
8. `controlNext_eq_nextState`;
9. current-output and `cpuregs_write` correspondence;
10. preservation of the aggregate-register state correspondence; and
11. recursive no-blackbox closure.

The child contracts should state these natural results directly. Parent proofs
should consume public child laws and should not unfold a child's gate-level
implementation.

The structural schedule should also mirror the explanation:

1. observe and split current state;
2. compute phase equality flags and simple shared predicates;
3. evaluate all phase transitions;
4. select the phase transition;
5. apply reset and alignment priority;
6. finish memory commands;
7. combine and capture next state; and
8. compute current-cycle outputs.

The schedule is proof data, not the meaning of the circuit. The simultaneous
structural equations remain authoritative.

## Reachability properties are separate

Useful system invariants include a recognized one-hot phase, well-formed
memory commands, sensible decoder class combinations, and alignment of active
requests. None may be assumed by the cycle certification because certification
must explain every structural state and every input.

After exact cycle certification, separate trace-level proofs should establish
that reset-reachable executions preserve:

- a recognized phase encoding;
- `Control.Commands.wellFormed` and therefore
  `Memory.CommandsWellFormed`;
- the intended command lifecycle; and
- phase-specific relationships among command and latch fields.

Keeping these theorems separate prevents a reachable-state argument from
hiding a mismatch between the concrete hardware and the total cycle contract.

## Implementation order and review gates

Once this document is accepted, implementation should proceed in proof-risk
order rather than by choosing the easiest visible block:

1. complete the source-to-contract assignment audit (done);
2. prove the arithmetic and exact-phase bridge lemmas (done);
3. declare the named `ControlState` and `Transition` layouts and prove their
   pack/unpack laws (done);
4. implement and certify `phaseDecode`, `alignment`, and `commandFinish`
   (done);
5. implement and certify the execute and memory phase children, where the
   highest-risk same-cycle priorities occur (done);
6. implement and certify the remaining phase children (done);
7. assemble and certify `PicoRVControlNext` (done and closed);
8. wrap it with aggregate storage and certify `PicoRVControl` (done);
9. prove recursive closure and closed FIRRTL rendering (done; CIRCT lowering
   also checked);
10. expand focused checks to cover every phase, selector priority, reset,
    misalignment, command clear/reassert case, and arbitrary-state default
    (done);
11. run the full Lean build and all generated-hardware regressions; and
12. only then replace the top-level Control blackbox.

Integration into `PicoRV` is a separate final step. A closed standalone Control
module should be reviewed before changing the core hierarchy.

## Completion criteria

Control is ready for top-level integration only when all of the following are
current and checked:

- the contract audit accounts for every configured upstream assignment;
- each proposed child has a natural contract and concrete certification;
- the aggregate structure implements `Control.cycleContract` for arbitrary
  inputs and states;
- reset and every competing-assignment priority have focused checks;
- command well-formedness remains a proved reachable invariant rather than an
  implementation assumption;
- the complete standalone hierarchy has no blackboxes;
- closed FIRRTL rendering and lowering succeed;
- the full Lean build and simulator suite pass; and
- top-level integration is performed in its own reviewable change.
