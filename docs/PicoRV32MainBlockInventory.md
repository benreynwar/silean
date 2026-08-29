# PicoRV32 configured main-block inventory

This inventory fixes the boundary between the sequencing controller and the
registered datapath before either contract is written. It was derived from the
declarations and assignments in the `// Main State Machine` region of
`picorv32.v`, with the parameter values in `PicoRV32TopLevelPlan.md` treated as
constants. Names below are source names; proposed Silean ports should preserve
them.

This is a hardware inventory, not a proposed contract state. Blocking
temporaries and combinational results are listed separately from edge-stored
state, and registers whose only enabled uses disappear after specialization
are explicitly excluded.

## Specialization result

| Owner | Live source state |
| --- | --- |
| `PicoRV32Control` | `cpu_state`, `latched_store`, `latched_stalu`, `latched_branch`, `latched_is_lu`, `latched_is_lh`, `latched_is_lb`, `latched_rd`, `mem_wordsize`, `mem_do_prefetch`, `mem_do_rinst`, `mem_do_rdata`, `mem_do_wdata`, `decoder_trigger`, `decoder_pseudo_trigger`, `trap` |
| `PicoRV32Datapath` | `reg_pc`, `reg_next_pc`, `reg_op1`, `reg_op2`, `reg_out`, `reg_sh`, `alu_out_q` |
| Existing children | decoder registers in `PicoRV32Decoder`, memory-interface registers in `PicoRV32Memory`, and architectural registers in `PicoRV32Regs` |

`trap` is an output register in the source and therefore control state, even
though it is also a top-level output. `reg_sh` is meaningful while an
iterative shift is active; its default unknown assignment outside that path
does not turn it into control state.

The following declared main-block registers are dead or constant in this
configuration and are not ported:

| Source names | Reason |
| --- | --- |
| `count_cycle`, `count_instr` | `ENABLE_COUNTERS = 0` |
| `irq_state`, `irq_delay`, `irq_active`, `irq_mask`, `irq_pending`, `timer` and IRQ temporaries | `ENABLE_IRQ = 0` |
| `pcpi_*` state | `ENABLE_PCPI = ENABLE_MUL = ENABLE_FAST_MUL = ENABLE_DIV = 0` |
| trace/debug state | `ENABLE_TRACE = 0`; simulation diagnostics are not hardware in the port |
| `latched_compr` | `COMPRESSED_ISA = 0`, so captured `compressed_instr` is always zero |
| `latched_trace` | `ENABLE_TRACE = 0` |
| `alu_out_0_q`, `alu_wait`, `alu_wait_2` | only semantically read by the disabled two-cycle ALU/compare paths |
| `decoder_trigger_q`, `decoder_pseudo_trigger_q` | their enabled functional reader is removed by `CATCH_ILLINSN = 1`; remaining uses are diagnostics |
| `clear_prefetched_high_word_q` | compressed-instruction buffering is disabled |
| `next_insn_opcode` | read only by debug/formal instrumentation excluded from this port |
| `instr_ecall_ebreak` | with `WITH_PCPI = 0` and `CATCH_ILLINSN = 1`, it has no functional reader; ECALL/EBREAK are already rejected by `instr_trap` |
| `mem_busy` | combinational command summary with no reader; retained only as a Lean semantic view, not a hardware port |

`current_pc`, `set_mem_do_rinst`, `set_mem_do_rdata`, and
`set_mem_do_wdata` use blocking assignments as same-cycle temporaries. They
are combinational values inside the relevant next-state logic, not state.
`alu_out`, `alu_out_0`, `alu_add_sub`, `alu_eq`, `alu_ltu`, `alu_lts`,
`alu_shl`, `alu_shr`, `cpuregs_write`, `cpuregs_wrdata`, and `next_pc` are also
combinational in this configuration.

## Why PC belongs to the datapath

There will not be a separate `PicoRV32Pc` child in the first port.
`reg_pc` and `reg_next_pc` form one value path with instruction results:

- sequential and JAL targets use `reg_pc`, `reg_next_pc`, and decoded
  immediates;
- JALR and taken branches select `reg_out` or `alu_out_q` through the same
  fetch-cycle logic that commits the next PC;
- effective-address, branch-result, link-value, and register-writeback paths
  already cross the proposed execution datapath; and
- the PC path has no independent start/done or fixed-latency interface.

A separate PC child would therefore expose most of the execution-result and
sequencing metadata again, or require new command signals not present in the
source. Keeping PC state in `PicoRV32Datapath` gives one coherent registered
instruction-value path while `PicoRV32Control` remains responsible for when
that path advances.

## Proposed direct crossing ports

These tables record logical direction. A signal used by more than one child is
wired directly to each consumer; it is not re-exported through control merely
to make a tree-shaped diagram.

### Control inputs

| Producer | Source-named values consumed by control |
| --- | --- |
| top level | `resetn` |
| decoder | `instr_jal`, `instr_jalr`, `instr_lb`, `instr_lbu`, `instr_lh`, `instr_lhu`, `instr_lw`, `instr_sb`, `instr_sh`, `instr_sw`, `instr_trap`, `is_lui_auipc_jal`, `is_lb_lh_lw_lbu_lhu`, `is_slli_srli_srai`, `is_jalr_addi_slti_sltiu_xori_ori_andi`, `is_sb_sh_sw`, `is_sll_srl_sra`, `is_beq_bne_blt_bge_bltu_bgeu`, `is_lbu_lhu_lw`, `decoded_rd` |
| datapath | `reg_pc`, `reg_op1`, `reg_sh`, `alu_out_0` |
| memory | `mem_done` |

Control uses `reg_pc` and `reg_op1` for configured instruction/data
misalignment traps, `reg_sh` to detect iterative-shift completion, and
`alu_out_0` to decide conditional branches.

### Control outputs

| Consumer | Source-named values produced by control |
| --- | --- |
| top level | `trap` |
| datapath | `cpu_state`, `latched_store`, `latched_stalu`, `latched_branch`, `latched_is_lu`, `latched_is_lh`, `latched_is_lb`, `mem_do_prefetch`, `mem_do_rdata`, `mem_do_wdata`, `decoder_trigger` |
| memory | `trap`, `mem_do_prefetch`, `mem_do_rinst`, `mem_do_rdata`, `mem_do_wdata`, `mem_wordsize` |
| decoder | `mem_do_rinst`, `decoder_trigger`, `decoder_pseudo_trigger` |
| register file | `cpuregs_write`, `latched_rd` |

`cpuregs_write` remains combinational control output. `latched_rd` is the
registered destination selected during fetch.

### Datapath inputs

| Producer | Source-named values consumed by datapath |
| --- | --- |
| top level | `resetn` |
| control | the values listed in the control-to-datapath row above |
| decoder | `instr_lui`, `instr_jal`, `instr_sub`, `instr_beq`, `instr_bne`, `instr_bge`, `instr_bgeu`, `instr_xori`, `instr_xor`, `instr_ori`, `instr_or`, `instr_andi`, `instr_and`, `instr_slli`, `instr_srli`, `instr_srai`, `instr_sll`, `instr_srl`, `instr_sra`, `is_lui_auipc_jal`, `is_lb_lh_lw_lbu_lhu`, `is_slli_srli_srai`, `is_jalr_addi_slti_sltiu_xori_ori_andi`, `is_lui_auipc_jal_jalr_addi_add_sub`, `is_slti_blt_slt`, `is_sltiu_bltu_sltu`, `is_compare`, `decoded_imm`, `decoded_imm_j`, `decoded_rs2` |
| register file | `cpuregs_rs1`, `cpuregs_rs2` |
| memory | `mem_done`, `mem_rdata_word` |

The detailed port declaration should retain the individual PicoRV32 Boolean
selectors rather than prematurely replacing them with a new opcode datatype.

### Datapath outputs

| Consumer | Source-named values produced by datapath |
| --- | --- |
| control | `reg_pc`, `reg_op1`, `reg_sh`, `alu_out_0` |
| memory | `next_pc`, `reg_op1`, `reg_op2` |
| register file | `cpuregs_wrdata` |

`next_pc` is the source combinational selection between `reg_next_pc` and the
completed branch/JALR result. `cpuregs_wrdata` is likewise the source
combinational selection among the link value, `alu_out_q`, and `reg_out`.
Both belong with the values they select, while their enables remain control.

### Direct paths that bypass control and datapath

`decoded_rs1` and `decoded_rs2` connect the decoder directly to the register
file. Memory's external ready/valid signals connect directly to top-level
ports. `mem_rdata_latched` and `mem_rdata_q` connect the memory region to the
decoder as in the existing decoder contract. These paths must not acquire
unnecessary forwarding ports on either new child.

The top-level `resetn` input fans out directly to every state-owning child,
including the decoder; it is not produced or forwarded by control.

## Same-cycle dependency review

After specialization the proposed boundary has no combinational cycle:

1. Decoder registered outputs, control state, datapath state, memory state,
   and register-file state are available at the start of the cycle.
2. Register-file reads depend only on registered decoder addresses and
   register-file state.
3. The combinational ALU depends on datapath state and registered decoder
   selectors; `alu_out_0` may feed control's next-state decision.
4. `next_pc` and `cpuregs_wrdata` depend on current datapath state and current
   registered control metadata.
5. Memory outputs depend on its current state, external inputs, current
   control commands, and current datapath address/data values. `mem_done` may
   feed both control and datapath next-state decisions.
6. Each child's edge update is then computed from those current-cycle values.

The apparent feedback paths all cross state: control command registers feed
memory, whose combinational `mem_done` determines later edge updates; and
datapath comparison feeds control's edge update, whose registered metadata
selects later datapath outputs. Per-output proof schedules may use this order,
but the schedules will remain proof inputs rather than module structure.

The contracts preserve this distinction directly. Control and decoder outputs
read only their current local state. Register-file reads depend on registered
decoder addresses. Datapath has separate rules for registered values,
`next_pc`, comparison, and writeback; in particular its comparison rule reads
only the six selectors that can affect `alu_out_0`. Memory has separate rules
for registered request values, each look-ahead value, status, formatted read
data, and latched read data. Thus `mem_done`, for example, does not acquire a
false dependency on datapath address or write-data signals.

`Silean/Examples/Checks/PicoRVBoundaryChecks.lean` maps every input of all five
children to one named child output or one of the three external inputs and
proves the endpoint signal types equal. Exhaustive pattern matching makes a
new input fail that check until its producer is explicitly classified. This
audit remains independent evidence for the typed wiring now constructed in
`Silean/Examples/PicoRV/PicoRV.lean`.

## Boundary conclusion

The top level therefore has five direct children:
`PicoRV32Control`, `PicoRV32Datapath`, `PicoRV32Memory`, `PicoRV32Decoder`, and
`PicoRV32Regs`. `PicoRV32Alu` is a combinational child of the datapath. There
is no separate PC child unless later implementation evidence reveals a
substantially cleaner source-faithful interface than this inventory.
