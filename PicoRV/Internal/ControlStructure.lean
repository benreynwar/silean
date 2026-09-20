import PicoRV.Control.ControlNext
import Silean.Authoring.ModuleDesign
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.Register.RegisterDerived
import Silean.Primitives.And
import Silean.Primitives.Or

namespace PicoRV

open Silean
open Silean.Authoring

/-! The standalone Control structure stores the complete named `ControlState`
in one aggregate register. Its current value drives both the public outputs
and the certified combinational `ControlNext`; the latter's result is captured
on the next edge. `cpuregs_write` remains combinational, exactly as in the
source, and is derived from the current phase and writeback latches. -/

module_design Control (name := "picorv32_control") where
  boundary (Control.ports) (naming := Control.Naming.ports)
  instances {
    inputsValue := Silean.Modules.NamedTupleCombiner.designWith
      Control.ControlInputs.signalMap Control.ControlInputs.schema,
    storage := Silean.Modules.Register.designWith Control.ControlState.schema,
    stateFields := Silean.Modules.NamedTupleSplitter.designWith
      Control.stateMap Control.ControlState.schema,
    next := Control.ControlNext.design,
    fetchPhase := Silean.Modules.EqualsConstant.design (.vector 8 .bit)
      (Control.stateBits Control.cpuStateFetch),
    writePending := Silean.Primitives.orDesign,
    cpuregsWrite := Silean.Primitives.andDesign }
  wiring {
  outputs {
    .cpuregs_write := cpuregsWrite.output,
    .cpu_state := stateFields[.cpu_state],
    .latched_store := stateFields[.latched_store],
    .latched_stalu := stateFields[.latched_stalu],
    .latched_branch := stateFields[.latched_branch],
    .latched_is_lu := stateFields[.latched_is_lu],
    .latched_is_lh := stateFields[.latched_is_lh],
    .latched_is_lb := stateFields[.latched_is_lb],
    .latched_rd := stateFields[.latched_rd],
    .mem_wordsize := stateFields[.mem_wordsize],
    .mem_do_prefetch := stateFields[.mem_do_prefetch],
    .mem_do_rinst := stateFields[.mem_do_rinst],
    .mem_do_rdata := stateFields[.mem_do_rdata],
    .mem_do_wdata := stateFields[.mem_do_wdata],
    .decoder_trigger := stateFields[.decoder_trigger],
    .decoder_pseudo_trigger := stateFields[.decoder_pseudo_trigger],
    .trap := stateFields[.trap] }
  instance (.inputsValue) {
    .resetn := input.resetn,
    .instr_jal := input.instr_jal,
    .instr_jalr := input.instr_jalr,
    .instr_lb := input.instr_lb,
    .instr_lbu := input.instr_lbu,
    .instr_lh := input.instr_lh,
    .instr_lhu := input.instr_lhu,
    .instr_lw := input.instr_lw,
    .instr_sb := input.instr_sb,
    .instr_sh := input.instr_sh,
    .instr_sw := input.instr_sw,
    .instr_trap := input.instr_trap,
    .is_lui_auipc_jal := input.is_lui_auipc_jal,
    .is_lb_lh_lw_lbu_lhu := input.is_lb_lh_lw_lbu_lhu,
    .is_slli_srli_srai := input.is_slli_srli_srai,
    .is_jalr_addi_slti_sltiu_xori_ori_andi :=
      input.is_jalr_addi_slti_sltiu_xori_ori_andi,
    .is_sb_sh_sw := input.is_sb_sh_sw,
    .is_sll_srl_sra := input.is_sll_srl_sra,
    .is_beq_bne_blt_bge_bltu_bgeu := input.is_beq_bne_blt_bge_bltu_bgeu,
    .is_lbu_lhu_lw := input.is_lbu_lhu_lw,
    .decoded_rd := input.decoded_rd,
    .reg_pc := input.reg_pc,
    .reg_op1 := input.reg_op1,
    .reg_sh := input.reg_sh,
    .alu_out_0 := input.alu_out_0,
    .mem_done := input.mem_done }
  instance (.storage) { .input := next.state }
  instance (.stateFields) { .value := storage.output }
  instance (.next) {
    .inputs := inputsValue.value,
    .current := storage.output }
  instance (.fetchPhase) { .value := stateFields[.cpu_state] }
  instance (.writePending) {
    .left := stateFields[.latched_branch],
    .right := stateFields[.latched_store] }
  instance (.cpuregsWrite) {
    .left := fetchPhase.result,
    .right := writePending.output }
  }

end PicoRV
