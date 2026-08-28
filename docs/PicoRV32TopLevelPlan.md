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

PCPI, IRQ, counter-CSR, and trace ports may therefore be absent from this
specialized module. Build the verification form with `RISCV_FORMAL`
observations enabled. Preserve both the ordinary memory interface and the
unconditionally present `mem_la_*` look-ahead interface.

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

The verification build additionally exposes the source RVFI names:

```text
rvfi_valid, rvfi_trap, rvfi_halt, rvfi_intr : bit
rvfi_order                                  : vector bit 64
rvfi_insn                                   : word32
rvfi_mode, rvfi_ixl                         : vector bit 2
rvfi_rs1_addr, rvfi_rs2_addr, rvfi_rd_addr : vector bit 5
rvfi_rs1_rdata, rvfi_rs2_rdata, rvfi_rd_wdata : word32
rvfi_pc_rdata, rvfi_pc_wdata                : word32
rvfi_mem_addr                               : word32
rvfi_mem_rmask, rvfi_mem_wmask              : vector bit 4
rvfi_mem_rdata, rvfi_mem_wdata              : word32
```

The final architectural specification is a retirement-trace relation over
RVFI observations, not a cycle contract that exposes internal state.

## Direct children

```text
picorv32
├── control  : PicoRV32Control
├── mem      : PicoRV32Memory
├── decoder  : PicoRV32Decoder
├── cpuregs  : PicoRV32Regs
├── alu      : PicoRV32Alu
└── rvfi     : PicoRV32Rvfi
```

These instance boundaries are introduced for the Silean port. `cpuregs`
retains the instance name used by PicoRV32 when an external register-file
module is selected. The other names follow headings and vocabulary in the
source.

Small primitives and reusable modules belong inside the state-owning or
combinational child whose behavior they implement. For example, the registers
implementing `reg_pc` and `reg_op1` are children of `control`, not siblings of
`control` at the `picorv32` top level.

## `control : PicoRV32Control`

This module ports the large main sequential state-machine block and the small
combinational selections directly associated with it. It owns:

- `cpu_state`;
- `reg_pc`, `reg_next_pc`, `reg_op1`, `reg_op2`, `reg_out`, and `reg_sh`;
- `latched_store`, `latched_stalu`, `latched_branch`, `latched_rd`,
  `latched_is_lu`, `latched_is_lh`, and `latched_is_lb`;
- `mem_do_prefetch`, `mem_do_rinst`, `mem_do_rdata`, `mem_do_wdata`, and
  `mem_wordsize`;
- `decoder_trigger`, `decoder_trigger_q`, `decoder_pseudo_trigger`, and
  `decoder_pseudo_trigger_q`; and
- any remaining enabled registers assigned by that same source block.

Disabled counter, IRQ, PCPI, compressed-instruction, and trace registers are
not ported.

Its inputs are the current outputs of the other source regions:

```text
decoder: instr_*, is_*, decoded_*, compressed_instr/instr_trap as applicable
cpuregs: cpuregs_rs1, cpuregs_rs2
alu:     alu_out, alu_out_0
mem:     mem_busy, mem_done, mem_rdata_word
top:     resetn
```

Its outputs are the source signals consumed elsewhere:

```text
to alu:      reg_op1, reg_op2 and relevant instr_*/is_* selectors
to mem:      next_pc, reg_op1, reg_op2, mem_do_*, mem_wordsize, trap
to decoder:  mem_do_rinst, mem_done/trigger-related control
to cpuregs:  cpuregs_write, cpuregs_wrdata, latched_rd
to rvfi:     current/writeback/debug facts needed by the source RVFI block
top:         trap
```

State is private to this module. A local exact-cycle specification may help
port and test the state machine, but higher-level users should rely on temporal
progress and retirement properties rather than a public state mapping.

The iterative shift transition remains here because PicoRV32 updates
`reg_op1`, `reg_sh`, `latched_store`, and `cpu_state` together in
`cpu_state_shift`. Reusable fixed shift and decrement children may implement
the datapath internally; a separate stateful top-level shifter would invent a
start/done boundary absent from the source.

## `mem : PicoRV32Memory`

This module ports the `// Memory Interface` region. It owns:

- `mem_state`, `mem_valid`, `mem_instr`, `mem_addr`, `mem_wdata`, and
  `mem_wstrb`;
- `mem_rdata_q` and response-capture state;
- look-ahead bookkeeping that remains relevant with `COMPRESSED_ISA = 0`; and
- any other register assigned by the enabled branches of the memory-region
  sequential blocks.

It accepts the source-named control and external inputs:

```text
resetn, trap
mem_do_prefetch, mem_do_rinst, mem_do_rdata, mem_do_wdata
next_pc, reg_op1, reg_op2, mem_wordsize
mem_ready, mem_rdata
```

It produces the ordinary and look-ahead memory ports plus `mem_busy`,
`mem_done`, `mem_rdata_word`, `mem_rdata_latched`, and
`next_insn_opcode` where those source signals cross into other regions.

Its natural public specification is temporal: a request remains stable while
stalled, accepted requests complete once, and load/store formatting matches
width and address. A private cycle description may mirror `mem_state` for its
structural proof. Load and store formatters are children inside `mem`.

## `decoder : PicoRV32Decoder`

This module ports the registered instruction-decoder blocks. It owns the
enabled `instr_*`, `is_*`, `decoded_rs1`, `decoded_rs2`, `decoded_rd`,
`decoded_imm`, `decoded_imm_j`, and related registered decode signals. It does
not own `decoder_trigger`; that register is updated in the main control block.

Its inputs are the exact source signals needed to update those registers,
principally `resetn`, `mem_do_rinst`, `mem_done`, `mem_rdata_latched`, and the
trigger state supplied by `control`. Outputs retain their original names.

Its specification should describe registered decode timing and provide a
natural Lean interpretation of the resulting signals. Public facts should
cover each supported RV32I encoding, immediate construction, legality, and the
mutual-exclusion assumptions used by PicoRV32's parallel cases.

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

This combinational module ports the enabled ALU region. Inputs retain
`reg_op1`, `reg_op2`, `instr_sub`, and the relevant `instr_*`/`is_*` selector
names. Outputs are `alu_out` and `alu_out_0`. There are no `alu_out_q` or
`alu_out_0_q` registers because `TWO_CYCLE_ALU = TWO_CYCLE_COMPARE = 0`.

Its natural specification is a total pure function interpreting the enabled
selector combinations. It should prove the selected result for addition,
subtraction, comparison, AND, OR, and XOR. Iterative shifts remain in
`control`. The implementation eventually uses reusable arithmetic, comparison,
and bitwise children.

## `rvfi : PicoRV32Rvfi`

This module ports the `RISCV_FORMAL` observation block and owns `rvfi_order`
and any other RVFI registers assigned there. It observes control, decoder,
register-file, and memory signals but does not influence functional execution.

Its contract should state how each completed PicoRV32 instruction produces an
RVFI event. This is a temporal observation contract, not necessarily a cycle
contract. The later architectural proof relates the emitted sequence to RV32I
instruction retirement and may use Sail through a narrow wrapper.

Keeping RVFI separate prevents verification bookkeeping from becoming core
state while preserving the source block that constructs it.

## State ownership summary

| Source state | Owning child |
| --- | --- |
| `cpu_state`, `reg_*`, `latched_*`, `mem_do_*`, decoder triggers | `control` |
| `mem_state`, memory request registers, captured memory data | `mem` |
| registered `instr_*`, `is_*`, and `decoded_*` signals | `decoder` |
| integer architectural registers | `cpuregs` |
| `rvfi_*` observation registers | `rvfi` |
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
control current-state outputs (`reg_*`, `mem_do_*`, selectors)
decoder current registered outputs
cpuregs combinational reads
alu combinational outputs
mem current/request/completion outputs
control next-state and writeback outputs
decoder/mem/cpuregs/control next states
rvfi observations and next state
top-level outputs
```

The detailed schedules belong to the certifications and may differ per output.
They are not stored in these module structures and do not define their
semantics.

## Blackbox staging

The first top-level composition may use behavioral guarantees for `mem`,
`decoder`, `cpuregs`, `alu`, and `rvfi` while their structures are developed.
`control` contains the central ported algorithm and should not remain an
assumption when claiming meaningful top-level progress.

There are two explicit statuses:

1. **Composition verified:** top-level properties follow assuming the stated
   child specifications.
2. **Structurally verified:** each assumed child guarantee has been discharged
   by a concrete certified Silean structure.

The appropriate specification form varies: pure combinational behavior for
`alu`, registered decode behavior for `decoder`, a stateful register-file
contract for `cpuregs`, temporal protocol behavior for `mem`, and retirement
traces for `rvfi` and the complete CPU.

## Work before implementation

1. Mechanically list every register assigned in the enabled source branches
   and assign it to exactly one child above.
2. Mechanically list signals crossing each proposed boundary and preserve
   their source names, widths, and directions.
3. Check that per-output schedules exist for the proposed bidirectional
   `control`/`mem` and `control`/`decoder` interfaces without altering timing.
4. Review those tables against `picorv32.v`; only then freeze child ports.
5. Implement the top-level composition using specification blackboxes, then
   port `control` instruction family by instruction family.

This inventory is the next design step. Sail integration and the final
retirement proof can wait until the hardware port has enough instruction
behavior to make them useful.
