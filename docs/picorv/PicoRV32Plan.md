# PicoRV32 port and verification plan

This is the authoritative plan for porting and verifying a small fixed
configuration of `picorv32.v`. The Silean design follows the source hardware:
source port, register, wire, and instance names are retained wherever they form
a structural boundary. Lean specifications may add natural views without
renaming the hardware being ported.

The child boundaries are new because PicoRV32 is mostly monolithic Verilog.
They follow existing source regions and state ownership rather than extracting
all state into an artificial top-level record.

## Fixed configuration

The first port specializes these parameters:

| Parameter | Value | Effect |
| --- | ---: | --- |
| `ENABLE_COUNTERS`, `ENABLE_COUNTERS64` | `0` | no counters or counter CSRs |
| `ENABLE_REGS_16_31` | `1` | all 32 integer registers |
| `ENABLE_REGS_DUALPORT` | `1` | two combinational register reads |
| `LATCHED_MEM_RDATA` | `0` | consume read data with `mem_ready` |
| `TWO_STAGE_SHIFT` | `1` | iterative shifts by four, then one |
| `BARREL_SHIFTER` | `0` | no barrel shifter |
| `TWO_CYCLE_COMPARE`, `TWO_CYCLE_ALU` | `0` | combinational compare and ALU |
| `COMPRESSED_ISA` | `0` | RV32I-width instructions only |
| `CATCH_MISALIGN`, `CATCH_ILLINSN` | `1` | trap misaligned and illegal operations |
| `ENABLE_PCPI`, `ENABLE_MUL`, `ENABLE_FAST_MUL`, `ENABLE_DIV` | `0` | no coprocessor, multiply, or divide |
| `ENABLE_IRQ`, `ENABLE_IRQ_QREGS`, `ENABLE_IRQ_TIMER` | `0` | no IRQ behavior |
| `ENABLE_TRACE` | `0` | no PicoRV32 trace port |
| `REGS_INIT_ZERO` | `0` | no register-file power-on initialization |
| `PROGADDR_RESET` | `0x00000000` | reset address |
| `STACKADDR` | `0xffffffff` | no reset write to `x2` |

IRQ-only address and mask parameters are irrelevant. `RISCV_FORMAL` and RVFI
instrumentation are not part of the emitted design. Reset remains the source's
active-low synchronous `resetn`, fanned out to every state-owning child.

## External boundary

The top level preserves PicoRV32's ordinary and look-ahead memory interfaces:

```text
inputs
  resetn, mem_ready : bit
  mem_rdata         : word32

outputs
  trap                         : bit
  mem_valid, mem_instr         : bit
  mem_addr, mem_wdata          : word32
  mem_wstrb                    : vector bit 4
  mem_la_read, mem_la_write    : bit
  mem_la_addr, mem_la_wdata    : word32
  mem_la_wstrb                 : vector bit 4
```

PicoRV32 does not distinguish RAM from memory-mapped I/O. `mem_instr`
distinguishes instruction fetch from data access. The environment used by the
eventual public theorem will classify addresses outside the core.

## Direct hierarchy

```text
picorv32
|- control  : PicoRV32Control
|- datapath : PicoRV32Datapath
|  `- alu   : PicoRV32Alu
|- mem      : PicoRV32Memory
|- decoder  : PicoRV32Decoder
`- cpuregs  : PicoRV32Regs
```

Small reusable arithmetic, logic, registers, and adapters belong inside the
subsystem whose source behavior they implement. Shared values fan out directly
to their consumers; they are not routed through control merely to make the
diagram tree-shaped.

`reg_pc` and `reg_next_pc` belong to the datapath. Sequential, branch, jump,
effective-address, link-value, and writeback paths share the same registered
value flow and do not have a clean independent protocol.

### State ownership

| Owner | Source state |
| --- | --- |
| control | `cpu_state`, sequencing `latched_*`, `mem_do_*`, `mem_wordsize`, decoder triggers, registered `trap` |
| datapath | `reg_pc`, `reg_next_pc`, `reg_op1`, `reg_op2`, `reg_sh`, `reg_out`, `alu_out_q` |
| memory | `mem_state`, request registers, `mem_rdata_q` |
| decoder | registered `instr_*`, `is_*`, register indices, and immediates |
| cpuregs | integer architectural registers |
| ALU | no state |

Disabled counter, IRQ, PCPI, compressed-instruction buffering, trace, and
formal-only registers are absent. Same-cycle blocking temporaries remain
combinational logic, not contract state.

## Current status

| Boundary | Contract | Concrete certified structure | Top-level use |
| --- | --- | --- | --- |
| ALU | exact pure cycle behavior and public operation laws | complete and closed | concrete nested datapath child |
| register file | exact read/write cycle behavior | complete and closed | concrete certified child |
| decoder | exact configured two-stage registered behavior | complete and closed, including match, immediate, and summary children | concrete certified child |
| memory | exact configured request-state behavior and natural protocol views | complete and closed standalone registered structure | concrete certified child |
| datapath | exact registered value-flow behavior | complete and closed standalone registered structure | concrete certified child |
| control | exact configured sequencing behavior | complete and closed standalone registered structure, including a closed certified next-state hierarchy | concrete certified child |
| top level | structural composition of the five child contracts | complete and recursively closed, with existence and uniqueness of structural solutions | all five direct children are concrete and certified |

The top-level `PicoRV/` library is a sibling client of the reusable `Silean/`
library rather than a Silean example subdirectory. `PicoRV/PicoRV.lean` is the
authoritative port map and wiring. It has
exactly the five direct children above. `PicoRVSchedule.lean` contains a
complete child-rule schedule and proves the simultaneous top-level equations
have exactly one solution. `PicoRVTopChecks.lean` recursively verifies that no
behavioral leaves remain. This is a checked composition boundary, not a CPU
correctness result.

## Child contracts and implementation plan

### Register file

`PicoRV32Regs` preserves `resetn`, `cpuregs_write`, `latched_rd`,
`cpuregs_wrdata`, `decoded_rs1`, `decoded_rs2`, `cpuregs_rs1`, and
`cpuregs_rs2`. It wraps `RegisterBank word32 5 2`, forces reads of `x0` to zero,
suppresses writes to `x0`, and suppresses writes while reset is asserted.
Other registers are not reset because `REGS_INIT_ZERO = 0`.

### ALU

`PicoRV32Alu` is combinational. It uses one `AddSub 32`, generic Equality,
bitwise logic, and muxes. The subtraction carry supplies unsigned no-borrow;
operand signs combine with that result for signed comparison. Shifts remain in
the iterative datapath because `BARREL_SHIFTER = 0`.

The total contract follows source selector priority and returns zero when no
result class is selected. Public laws cover legal ADD, SUB, comparisons, XOR,
OR, and AND without exposing internal gates or muxes.

### Decoder

The decoder contract preserves two independently enabled registered stages.
Capture records opcode classes, register indices, and jump immediate from a
completed instruction read. Resolve records detailed instruction flags and
the remaining immediate. Simultaneous enables read the same pre-edge state,
matching Verilog nonblocking assignments. The structure retains the
source one-hot signals; natural decode theorems can provide an instruction
view and mutual-exclusion facts.

The parent has this certified two-child hierarchy. Both stages and all three
resolve-stage children are concrete, certified, and recursively closed:

```text
PicoRV32Decoder
|- capture : DecoderCaptureStage
`- resolve : DecoderResolveStage
   |- match     : DecoderInstructionMatch (concrete and closed)
   |- immediate : DecoderImmediate (concrete and closed)
   `- summary   : DecoderInstructionSummary (concrete and closed)
```

`DecoderCaptureStage` owns 14 registers: the four directly recognized
LUI/AUIPC/JAL/JALR flags, five broad opcode classes, three register addresses,
the J immediate, and `compressed_instr`. Its common capture condition is
`mem_do_rinst && mem_done`; compressed-instruction behavior remains fixed off.
The branch-class register also applies the source's reset override.
Its concrete certified structure uses generic slices, fixed-value equality,
Boolean gates, signal adapters, and registers. The generated FIRRTL hierarchy
is closed and lowers successfully through CIRCT.

`DecoderResolveStage` owns 45 registered second-stage results. The
ECALL/EBREAK predicate is retained as private state because the source decodes
it explicitly. It is deliberately omitted from the recognized-instruction OR,
causing ECALL and EBREAK to enter the configured trap path, and is not consumed
as a separate top-level decoder output.
`DecoderInstructionMatch` takes only the instruction word, the five captured
opcode classes, and captured JALR. It produces the 35 configured exact
instruction predicates (including ECALL/EBREAK and FENCE) and the three
same-cycle shift/non-shift groups. Disabled counter, IRQ, PCPI, and compressed
predicates do not appear at its boundary.

`DecoderImmediate` takes the instruction word, captured J immediate, and the
captured classes that select J/I/B/S/U formats. Its natural Lean behavior is
`Option Word`; its ports expose that as `valid` and `value`. An invalid
selection tells the resolve stage to retain `decoded_imm`, rather than assigning
a fabricated value for the source don't-care case. Its priority is J, U, I, B,
then S, matching the source `case (1'b1)`. Its concrete certified structure
uses four bit-vector layouts, OR gates, a zero constant, and five priority
muxes. Its complete hierarchy is proven to contain no blackboxes.

`DecoderInstructionSummary` takes the current pre-edge exact instruction flags,
the four captured direct flags, and the broad branch class. It produces the six
summary values assigned unconditionally each cycle and the configured
continuous `instr_trap` result. Consequently it does not consume the newly
computed match results on the same edge.

The resolve stage owns all priority between ordinary summary updates, a
resolve trigger, and reset. In particular, the ordinary summary values are
formed from pre-edge flags, `decoder_trigger && !decoder_pseudo_trigger` then
forces `is_lui_auipc_jal_jalr_addi_add_sub` and `is_compare` low, and reset has
final priority for the selectively cleared registers. If capture and resolve
fire together, resolve consumes the old capture-stage outputs, not values
captured on the same edge.

All three children are combinational zero-state cycle contracts. Their sole
rules explicitly read their complete input boundaries and write their complete
output boundaries. They contain no decoder trigger, pseudo-trigger, reset, or
state: those dependencies and priorities remain visible in the resolve parent.

The stage modules are PicoRV-private architectural components, not proposed
general-purpose helpers. Their internal structures should use generic
registers, muxes, reductions, gates, constants, equality, and aggregate
adapters. A generic vector slice and equality-with-constant composition may be
added first if their contracts and naming materially simplify this structure;
neither should contain decoder-specific behavior.

### Memory interface

The memory contract preserves the configured single-outstanding request state
machine, ordinary `mem_*`, and look-ahead `mem_la_*` behavior. It includes
request, transfer, and completion views. `CommandsWellFormed` permits
prefetch/instruction-read promotion but rejects overlap with data commands.
The control proof must establish that discipline. Formatting claims assume
the live word-size encodings 0, 1, or 2; the two-state contract totalizes the
source don't-care encoding 3.

The source audit, proposed aggregate-register hierarchy, natural proof
argument, priority details, and verification coverage are recorded in
[`PicoRVMemoryPlan.md`](PicoRVMemoryPlan.md). The transition hierarchy is
implemented before the simpler formatting logic because reset/trap response
capture and delayed prefetch completion carry the greatest semantic risk.

### Datapath

The datapath owns PC, operands, iterative shift state, result state, and the
captured ALU result. Its contract has separate rules for current registered
values, next PC, comparison, and writeback. Comparison inherits the certified
ALU's bundled selector dependency, which is coarser than its Boolean result
alone but compatible with the parent schedule. The closed structure contains
the certified ALU and implements effective addresses, load formatting, result capture, and
the configured four-then-one iterative shift. The source audit, implemented
hierarchy, universal proof argument, and verification coverage are recorded in
[`PicoRVDatapathPlan.md`](PicoRVDatapathPlan.md).

### Control

Control owns instruction sequencing, memory commands, decoder triggers,
writeback metadata, and trap. Its contract covers fetch, operand collection,
execute/branch, iterative shift, load/store, illegal or misaligned trap, and
request completion. The structure should remain close to the source state
machine rather than replacing it with a newly invented controller protocol.
The proposed semantic decomposition, module hierarchy, and correctness
argument are recorded in [`PicoRVControlPlan.md`](PicoRVControlPlan.md). That
document is the review record for the completed standalone structure and its
completed top-level integration. Reachability work remains separate.

## Same-cycle dependency discipline

The child graph has paths in both directions but no intended combinational
cycle:

1. registered control, decoder, datapath, memory, and register-file state is
   available at cycle start;
2. register reads use registered decoder addresses;
3. the ALU uses current datapath operands and registered decoder selectors;
4. comparison may affect control next state;
5. memory completion may affect control and datapath next state; and
6. all child state transitions consume those current-cycle results.

Per-output rules preserve these narrow dependencies. Proof schedules express a
valid order for the required facts but do not define hardware semantics.
`PicoRVBoundaryChecks.lean` independently classifies every child input by its
producer and verifies its signal shape.

## Verification stages

The intended first refinement slices and the complete simulation obligations
are detailed in [`PicoRVRefinementPlan.md`](PicoRVRefinementPlan.md).

### 1. Close the structure (complete)

Implement and certify decoder, memory, datapath, and control against their
existing contracts. Replace each top-level blackbox with its certified
structure. The milestone ends with a recursive no-blackbox proof and the same
source-facing external boundary.

### 2. Define architectural observation

Do not require a snapshot mapping from all microarchitectural registers to
architectural state. There may be no cycle at which every physical register is
simultaneously an architectural snapshot.

Instead define a proof-level retirement observation using existing execution
state and completed bus operations. It is not an emitted RVFI interface.
Internal lemmas should relate completed instruction and data transactions to
architectural fetches, loads, and stores.

### 3. Connect RV32I semantics

Use the sibling `sail-riscv32-lean` port through a narrow adapter that exposes
the RV32I instruction step needed here. The Sail-derived state transition is
the architectural reference; Silean supplies the microarchitectural trace and
retirement reconstruction.

Prove that each reconstructed retirement corresponds to the reference step,
with silent implementation cycles between retirements. This stronger internal
trace should account for register and ordinary-memory effects even if the
public theorem observes less.

### 4. State the public theorem at the boundary

Compose the core with a memory/address-classification environment. The desired
public claim is that, after reset, the sequence of memory-mapped-I/O operations
and termination/trap behavior agrees with RV32I execution. Ordinary-memory
transaction correspondence remains available to rule out a processor that
obtains the right I/O trace through an invalid memory transformation.

Nonterminating programs are observed through their I/O traces. Programs that
terminate without externally visible effects are intentionally outside the
weakest public observation unless a stronger theorem is requested.

## Source-of-truth files

- `PicoRV/*.lean`: boundaries and contracts;
- `PicoRV.lean`: exact top-level ports and wiring;
- `PicoRVSchedule.lean`: proof schedule for the staged composition;
- `tests/picorv/lean/PicoRVTests/*Checks.lean`: focused behavioral and boundary
  checks; and
- the configured upstream `picorv32.v`: final authority for source behavior.

When this document conflicts with the Lean port maps, the code describes the
current implementation and the discrepancy should be reviewed against the
configured Verilog rather than silently preserving the prose.
