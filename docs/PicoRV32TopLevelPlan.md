# PicoRV32 top-level implementation plan

This is the concrete first plan for directly porting a simple configuration of
`picorv32.v`. The design follows the source's hardware organization. State
remains inside the subsystem that owns and updates it; it is not extracted into
a top-level aggregate state register.

Existing PicoRV32 module, port, register, and wire names are preserved in the
structural design. Lean specifications may add meaningful views and datatypes
without renaming the hardware being ported. The submodule boundaries below are
new—the original is mostly monolithic—but each boundary follows an existing
Verilog region and the signals that cross into or out of it.

The configured main-block register and crossing-signal audit is recorded in
`PicoRV32MainBlockInventory.md`; it is authoritative for the control/datapath
boundary summarized here.

## Fixed source configuration

The first port specializes `picorv32` to:

| Parameter | Value | Consequence |
| --- | ---: | --- |
| `ENABLE_COUNTERS` | `0` | no cycle/instruction counters |
| `ENABLE_COUNTERS64` | `0` | irrelevant with counters disabled |
| `ENABLE_REGS_16_31` | `1` | all 32 architectural register addresses |
| `ENABLE_REGS_DUALPORT` | `1` | two combinational register reads |
| `LATCHED_MEM_RDATA` | `0` | consume read data with `mem_ready` |
| `TWO_STAGE_SHIFT` | `1` | iterative shift by four, then one |
| `BARREL_SHIFTER` | `0` | no barrel shifter |
| `TWO_CYCLE_COMPARE` | `0` | combinational comparison |
| `TWO_CYCLE_ALU` | `0` | combinational ALU |
| `COMPRESSED_ISA` | `0` | 32-bit RV32I instructions only |
| `CATCH_MISALIGN` | `1` | misaligned accesses trap |
| `CATCH_ILLINSN` | `1` | illegal instructions trap |
| `ENABLE_PCPI` | `0` | no external coprocessor |
| `ENABLE_MUL` | `0` | no multiplier |
| `ENABLE_FAST_MUL` | `0` | no fast multiplier |
| `ENABLE_DIV` | `0` | no divider |
| `ENABLE_IRQ` | `0` | no IRQ behavior or custom IRQ instructions |
| `ENABLE_IRQ_QREGS` | `0` | irrelevant with IRQ disabled |
| `ENABLE_IRQ_TIMER` | `0` | irrelevant with IRQ disabled |
| `ENABLE_TRACE` | `0` | no PicoRV32 trace behavior |
| `REGS_INIT_ZERO` | `0` | no register-file power-on initialization |
| `MASKED_IRQ` | `0x00000000` | irrelevant with IRQ disabled |
| `LATCHED_IRQ` | `0xffffffff` | irrelevant with IRQ disabled |
| `PROGADDR_RESET` | `0x00000000` | reset address |
| `PROGADDR_IRQ` | `0x00000010` | irrelevant with IRQ disabled |
| `STACKADDR` | `0xffffffff` | no special reset write to `x2` |

PCPI, IRQ, counter-CSR, trace, and `RISCV_FORMAL` instrumentation are absent
from this specialized module. Preserve both the ordinary memory interface and
the unconditionally present `mem_la_*` look-ahead interface.

Reset remains the source's active-low synchronous `resetn`. Each state-owning
child receives `resetn` and implements the reset behavior of its corresponding
`always @(posedge clk)` block. There is no top-level aggregate reset register.

## External ports

The functional ports are:

```text
inputs
  resetn, mem_ready : bit
  mem_rdata         : word32

outputs
  trap                    : bit
  mem_valid, mem_instr    : bit
  mem_addr, mem_wdata     : word32
  mem_wstrb               : vector bit 4
  mem_la_read, mem_la_write : bit
  mem_la_addr, mem_la_wdata : word32
  mem_la_wstrb              : vector bit 4
```

The eventual public correctness theorem will observe memory-mapped-I/O and
termination/trap behavior after composing the core with an external address
decoder and memory environment. PicoRV32 itself does not distinguish ordinary
RAM from memory-mapped I/O; `mem_instr` distinguishes instruction fetches from
data accesses only. A stronger correspondence between completed data-memory
transactions and architectural loads/stores will probably be used internally
to prove the public theorem. It will not port or emit PicoRV32's `RISCV_FORMAL`
RVFI instrumentation.

## Direct children

```text
picorv32
├── control  : PicoRV32Control
├── datapath : PicoRV32Datapath
├── mem      : PicoRV32Memory
├── decoder  : PicoRV32Decoder
└── cpuregs  : PicoRV32Regs
```

These instance boundaries are introduced for the Silean port. `cpuregs`
retains the instance name used by PicoRV32 when an external register-file
module is selected. The other names follow headings and vocabulary in the
source.

Small primitives and reusable modules belong inside the subsystem whose
hardware behavior they implement. State follows the value path that owns it:
registering an intermediate datapath value does not by itself make that
register control state.

## `control : PicoRV32Control`

The contract for this module is defined in `Examples/PicoRV/Control.lean`.
This module owns sequencing: which phase the processor is in, which operation
may advance, and which child is commanded on the current cycle. It owns:

- `cpu_state`;
- `latched_store`, `latched_stalu`, `latched_branch`, `latched_rd`,
  `latched_is_lu`, `latched_is_lh`, and `latched_is_lb`;
- `mem_do_prefetch`, `mem_do_rinst`, `mem_do_rdata`, `mem_do_wdata`, and
  `mem_wordsize`;
- `decoder_trigger` and `decoder_pseudo_trigger`; and
- the registered top-level `trap` output.

Disabled counter, IRQ, PCPI, compressed-instruction, and trace registers are
not ported.

Its inputs are the current outputs of the other source regions, including
datapath completion and condition results:

```text
decoder: enabled instr_*/is_* classifiers, instr_trap, decoded_rd
datapath: reg_pc, reg_op1, reg_sh, alu_out_0
mem:     mem_done
top:     resetn
```

Its outputs are the source signals consumed elsewhere:

```text
to datapath: cpu_state, registered writeback/load metadata, memory command state,
             decoder_trigger
to mem:      mem_do_*, mem_wordsize, trap
to decoder:  mem_do_rinst, decoder_trigger, decoder_pseudo_trigger
to cpuregs:  cpuregs_write, latched_rd
top:         trap
```

Decoder selectors and register-file values connect directly to the datapath;
memory data also connects directly to it. Control does not forward values it
does not interpret.

State is private to this module. A local exact-cycle specification may help
port and test the state machine, but higher-level users should rely on temporal
progress and retirement properties rather than a public state mapping.

The control contract should expose sequencing facts, not duplicate arithmetic
or value-flow behavior. In particular, the iterative shift's variable latency
crosses this boundary: control starts and advances it, while the datapath owns
the shifting value and count.

The exact transition preserves the source's nonblocking timing and the final
priority of its common memory-command clear/set logic. It covers reset, trap,
fetch and decoder handoff, both operand-load phases, execute and branch
coordination, iterative-shift completion, load/store issue and completion,
decoder pseudo-triggers, misalignment traps, and registered writeback
metadata. `cpuregs_write` is a combinational view of current control state.

The contract also exposes the memory-command compatibility predicate and a
theorem equating it with `PicoRV32Memory.CommandsWellFormed`. Data read and
write commands are exclusive with all others, but `mem_do_prefetch` and
`mem_do_rinst` may be asserted together: this is how the source promotes a
prefetch. Focused checks cover reset, promotion, completion, and invalid data
overlap. A global invariant is necessarily reset-reachable rather than a fact
about arbitrary cycle-contract state, so it belongs in the later top-level
trace proof.

## `datapath : PicoRV32Datapath`

The contract for this module is defined in `Examples/PicoRV/Datapath.lean`.
This module owns the execution values that flow through several processor
cycles: `reg_pc`, `reg_next_pc`, `reg_op1`, `reg_op2`, `reg_sh`, `reg_out`, and
`alu_out_q`. It contains
the combinational `PicoRV32Alu` child and implements ALU execution, iterative
shifting, effective-address calculation, and the common result path used for
writeback.

This is not a separately invented accelerator protocol. Its ports should be
the source-named values and enables already crossing the relevant regions of
`picorv32.v`. For an ordinary ALU operation the contract can state the exact
registered result timing. For iterative shifts it should state that a start
event eventually produces the mathematical RV32 shift result; the latency
depends on the shift amount because the configured implementation shifts by
four and then by one.

`reg_pc` and `reg_next_pc` belong to this datapath. Sequential, JAL, JALR, and
branch PC flow shares decoder inputs and the common execution-result path, and
has no independent protocol. A separate PC child would therefore add a broad
artificial interface rather than isolate a source subsystem.

The exact state transition specializes the source's main state-machine block:
only `reg_pc` and `reg_next_pc` reset; `alu_out_q` captures the current
combinational ALU result on every edge; and each enabled processor phase
updates only its live datapath registers. Source `x` assignments are
totalized by retaining the previous value, which constrains no live use.

The output contract is deliberately divided by real dependencies. Current
`reg_pc`, `reg_op1`, `reg_op2`, and `reg_sh` read state only; `next_pc` reads branch
metadata; `alu_out_0` reads the comparison selectors; and `cpuregs_wrdata`
reads writeback metadata. Memory completion and register-file data are needed
for the state transition but not falsely attached to every current output.

Focused checks cover reset, sequential and JAL PC updates, JALR/branch target
selection, immediate and register operand capture, ALU-result capture, load
and store effective addresses, signed/unsigned load results, writeback, and
iterative logical/arithmetic shifting. A nine-bit shift demonstrates the
configured four/four/one sequence followed by the result-capture cycle. No
`ModuleStructure` or certification exists yet.

## `mem : PicoRV32Memory`

The contract for this module is defined in `Examples/PicoRV/Memory.lean`. It
ports the live behavior of the `// Memory Interface` region after specializing
`COMPRESSED_ISA = 0` and `LATCHED_MEM_RDATA = 0`. It owns:

- `mem_state`, `mem_valid`, `mem_instr`, `mem_addr`, `mem_wdata`, and
  `mem_wstrb`;
- `mem_rdata_q`.

`mem_rdata_word`, `mem_rdata_latched`, `mem_busy`, `mem_done`, and all
`mem_la_*` values are combinational, even where Verilog uses `reg` as an
assignment-category keyword. `mem_wordsize` and the four `mem_do_*` commands
are assigned by control and cross into this child as inputs. The source still
declares compressed-instruction bookkeeping such as `mem_la_secondword`,
`mem_la_firstword_reg`, `last_mem_valid`, `prefetched_high_word`, and
`mem_16bit_buffer`; every live use is disabled in the fixed configuration, so
these dead registers are not state of the specialized child.

It accepts the source-named control and external inputs:

```text
resetn, trap
mem_do_prefetch, mem_do_rinst, mem_do_rdata, mem_do_wdata
next_pc, reg_op1, reg_op2, mem_wordsize
mem_ready, mem_rdata
```

It produces the registered ordinary memory request, combinational look-ahead
ports, `mem_done`, formatted `mem_rdata_word`,
`mem_rdata_latched` and `mem_rdata_q`.

The exact cycle contract mirrors the four source phases: idle, read request,
write request, and transferred prefetch. Its separate natural protocol view
represents the sole external request as an `Option Request`. Public laws prove
that this request is stable while stalled, that no ordinary completion occurs
without a transfer, that an active instruction/data read or write completes on
its transfer and returns idle, and that a pure prefetch transfer instead
completes exactly once when a later `mem_do_rinst` consumes it without another
external transfer. This distinction is required by the Verilog.

The source requires data reads and writes to be exclusive with all other
commands, while allowing `mem_do_prefetch` and `mem_do_rinst` together during
prefetch promotion. Commands remain asserted as required and are dropped after
`mem_done`. `CommandsWellFormed` names this compatibility condition;
`InputsWellFormed` additionally requires the source's live `mem_wordsize`
encodings 0, 1, or 2. Encoding 3 reaches a Verilog `full_case` don't-care; the
two-state contract totalizes it with word formatting, while every public
formatting claim assumes `InputsWellFormed`. The eventual control contract must
prove the full caller discipline. Without deassertion, a held level command
correctly starts a new request after the memory state returns idle, so an
unconditional global “one completion ever” claim would be false.

Synchronous active-low reset sets `mem_state` to idle and clears `mem_valid`.
Other request and captured-data registers retain their values. `trap` stops
state-machine progress and clears `mem_valid` only when `mem_ready` permits the
outstanding external transfer to finish, exactly as in the source. Focused
checks cover stalls, transfer/completion, instruction/data classification,
word/half/byte formatting and lanes, response capture, prefetch promotion, and
reset. No memory `ModuleStructure` exists yet.

## `decoder : PicoRV32Decoder`

The contract for this module is defined in `Examples/PicoRV/Decoder.lean`. It
owns the live registered instruction-decoder state: enabled `instr_*`, `is_*`,
`decoded_rs1`, `decoded_rs2`, `decoded_rd`, `decoded_imm`, `decoded_imm_j`, and
`compressed_instr`. Only signals read outside the decoder are exported as
ports; intermediate opcode-class and recognition registers remain private.
It does not own
`decoder_trigger` or `decoder_pseudo_trigger`; those registers are updated in
the main control block.

Its exact source-facing inputs are:

```text
resetn, mem_do_rinst, mem_done, mem_rdata_latched,
decoder_trigger, decoder_pseudo_trigger, mem_rdata_q
```

The behavior has two independently enabled registered stages. On
`mem_do_rinst && mem_done`, the capture stage records opcode classes, register
indices, `decoded_imm_j`, and the always-false specialized
`compressed_instr`. On `decoder_trigger && !decoder_pseudo_trigger`, the
resolve stage uses the previously captured classes and `mem_rdata_q` to record
the detailed instruction flags and `decoded_imm`. If both stages fire on one
edge, all right-hand sides observe the same pre-edge state, matching Verilog
nonblocking assignments.

Six summary flags are assigned unconditionally from the previous detailed
flags. The resolve block then clears two of them, so their apparent extra cycle
of latency is intentional source behavior. Active-low `resetn` is synchronous
and clears only the subset explicitly cleared by `picorv32.v`; the remaining
decoder registers stay unconstrained until written. `instr_trap` is a
combinational output over the registered recognized-instruction flags rather
than decoder state. In the Verilog default branch, `decoded_imm` is `x`; the
two-state contract chooses its previous value there, which is permitted by the
source's don't-care and creates no additional externally required behavior.

Focused checks cover capture and resolve timing, all five RV32I immediate
layouts, the delayed summary update, partial reset, and recognized versus
illegal instruction output. No decoder `ModuleStructure` exists yet.

## `cpuregs : PicoRV32Regs`

This module owns the integer-register storage and preserves PicoRV32's signal
names:

```text
inputs:  resetn, cpuregs_write, latched_rd, cpuregs_wrdata,
         decoded_rs1, decoded_rs2
outputs: cpuregs_rs1, cpuregs_rs2
```

It has two combinational reads and one synchronous write. Address zero reads
as zero, and a write with `latched_rd = 0` has no effect. With
`REGS_INIT_ZERO = 0`, reset does not initialize the other architectural
registers. The natural specification describes architectural register values,
not mux-tree or storage hierarchy.

Its implementation can use a generic multi-read register bank without
duplicating storage. This is a good initial specification blackbox while that
reusable bank is developed.

## `alu : PicoRV32Alu`

This combinational child of `PicoRV32Datapath` ports the enabled ALU region. Inputs retain
`reg_op1`, `reg_op2`, `instr_sub`, and the relevant `instr_*`/`is_*` selector
names. Outputs are `alu_out` and `alu_out_0`. The ALU itself has no state
because `TWO_CYCLE_ALU = TWO_CYCLE_COMPARE = 0`. The source nevertheless
captures `alu_out` in `alu_out_q`; that following-cycle value belongs to the
datapath, not to this combinational child.

Its natural specification is a total pure function interpreting the enabled
selector combinations. It should prove the selected result for addition,
subtraction, comparison, AND, OR, and XOR. The implementation eventually uses reusable arithmetic, comparison,
and bitwise children.

## State ownership summary

| Source state | Owning child |
| --- | --- |
| `cpu_state`, sequencing `latched_*`, `mem_do_*`, decoder triggers | `control` |
| `reg_op1`, `reg_op2`, `reg_sh`, `reg_out`, `alu_out_q` | `datapath` |
| `reg_pc`, `reg_next_pc` | `datapath` |
| `mem_state`, memory request registers, captured memory data | `mem` |
| registered `instr_*`, `is_*`, and `decoded_*` signals | `decoder` |
| integer architectural registers | `cpuregs` |
| ALU | stateless |

This ownership should be checked mechanically against assignments in the
configured Verilog before implementation. No register should be duplicated or
moved merely to make a child interface smaller.

## Same-cycle dependency structure

The source contains paths in both directions between conceptual regions, but
they are not combinational cycles because some outputs depend only on current
local state and other outputs are produced later. Silean's per-output rules and
schedules should express that distinction rather than changing the hardware.

A representative order is:

```text
control current-state outputs (`mem_do_*`, enables, selectors)
decoder current registered outputs
cpuregs combinational reads
datapath current values and ALU combinational outputs
mem current/request/completion outputs
control decisions and datapath/writeback outputs
decoder/mem/cpuregs/datapath/control next states
top-level outputs
```

The detailed schedules belong to the certifications and may differ per output.
They are not stored in these module structures and do not define their
semantics.

## Blackbox staging

The first top-level composition may use behavioral guarantees for `mem`,
`decoder`, `cpuregs`, `datapath`, and `alu` while their structures are developed.
`control` contains the central ported algorithm and should not remain an
assumption when claiming meaningful top-level progress.

There are two explicit statuses:

1. **Composition verified:** top-level properties follow assuming the stated
   child specifications.
2. **Structurally verified:** each assumed child guarantee has been discharged
   by a concrete certified Silean structure.

The appropriate specification form varies: pure combinational behavior for
`alu`, registered decode behavior for `decoder`, a stateful register-file
contract for `cpuregs`, and temporal protocol behavior for `mem`. Retirement
is a semantic property of the complete CPU rather than another hardware child.

## Boundary review status

All five direct-child cycle contracts now exist. The joint review against the
fixed configuration of `picorv32.v` is recorded in
`PicoRV32MainBlockInventory.md`. A focused Lean check exhaustively maps every
child input to its named producer and verifies matching signal types. Output
rules preserve the actual same-cycle dependencies, so later proof schedules
will not be forced through unrelated inputs.

The configured top-level `ModuleStructure` is now implemented in
`Examples/PicoRV/PicoRV.lean` with exactly these five contract-backed blackbox
children. `PicoRVSchedule.lean` supplies proof-only parent-output,
child-state-input, and complete-rule schedules and proves uniqueness of
structural solutions. This is composition verification, not a claim that any
child has a concrete structure or that the CPU is architecturally correct.
Sail integration and the retirement proof remain later work.

### Assembled-boundary review

The implemented boundary was checked again against the configured regions of
`picorv32.v`, rather than only against the earlier planning table:

- the external inputs and outputs match the source's reset, ordinary memory,
  look-ahead memory, and trap ports; `clk` remains Silean's implicit global
  clock, while disabled PCPI, IRQ, trace, and formal ports are absent;
- every input of `control`, `datapath`, `mem`, `decoder`, and `cpuregs` is
  supplied exactly once by either a top-level input or the source-owning child;
- all eleven functional outputs are driven by the same owning region as in the
  source (`trap` by control and both memory interfaces by `mem`); and
- no forwarding-only ports or duplicate state owners were introduced.

The exhaustive `Wiring` definition makes missing sinks a type error, while
`PicoRVBoundaryChecks.lean` independently checks the producer classification
and signal shapes. `PicoRVTopChecks.lean` checks the constructed blackbox
children and completed schedules.
