import Silean.Examples.PicoRV.Decoder.DecoderResolveStage
import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatch
import Silean.Examples.PicoRV.Decoder.DecoderImmediate
import Silean.Examples.PicoRV.Decoder.DecoderInstructionSummary
import Silean.Contracts.Cycle.CycleBlackbox
import Silean.Authoring.ModuleDesign
import Silean.Modules.EnabledRegister.EnabledRegister
import Silean.Modules.EnabledResetRegister.EnabledResetRegister
import Silean.Modules.Register.Register
import Silean.Modules.ResetRegister.ResetRegister
import Silean.Modules.Mux.Mux
import Silean.Modules.Constant.Constant
import Silean.Primitives.Not
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace Silean.Examples.PicoRV.Decoder.ResolveStage

open Silean
open Silean.Authoring
open Silean.Examples.PicoRV.Decoder

/-! ## Structural implementation

The 45 logical contract registers are grouped into six aggregate storage
instances. This grouping is structural only; the public contract retains the
source Verilog's individual state names and update behavior.

The three combinational decoder children remain explicit blackboxes at this
stage. Their public contracts, rather than their future implementations, are
the only facts used by this parent. -/

private def resetMatchRegisters : List Register := [
  .instr_beq, .instr_bne, .instr_blt, .instr_bge, .instr_bltu, .instr_bgeu,
  .instr_addi, .instr_slti, .instr_sltiu, .instr_xori, .instr_ori, .instr_andi,
  .instr_add, .instr_sub, .instr_sll, .instr_slt, .instr_sltu, .instr_xor,
  .instr_srl, .instr_sra, .instr_or, .instr_and, .instr_fence]

private def retainedMatchRegisters : List Register := [
  .instr_lb, .instr_lh, .instr_lw, .instr_lbu, .instr_lhu,
  .instr_sb, .instr_sh, .instr_sw,
  .instr_slli, .instr_srli, .instr_srai, .instr_ecall_ebreak,
  .is_slli_srli_srai, .is_jalr_addi_slti_sltiu_xori_ori_andi,
  .is_sll_srl_sra]

private def ordinarySummaryRegisters : List Register := [
  .is_lui_auipc_jal, .is_slti_blt_slt, .is_sltiu_bltu_sltu, .is_lbu_lhu_lw]

@[simp] private theorem resetMatchRegisters_length : resetMatchRegisters.length = 23 := rfl
@[simp] private theorem retainedMatchRegisters_length : retainedMatchRegisters.length = 15 := rfl
@[simp] private theorem ordinarySummaryRegisters_length : ordinarySummaryRegisters.length = 4 := rfl

private def resetMatchRegister (index : Fin 23) : Register :=
  resetMatchRegisters[index]

private def retainedMatchRegister (index : Fin 15) : Register :=
  retainedMatchRegisters[index]

private def ordinarySummaryRegister (index : Fin 4) : Register :=
  ordinarySummaryRegisters[index]

def resetMatchType : SignalType := .vector 23 .bit
def retainedMatchType : SignalType := .vector 15 .bit
def ordinarySummaryType : SignalType := .vector 4 .bit
def immediateType : SignalType := .vector 32 .bit

def falseResetMatches : resetMatchType.Denote := fun _ => false

private def matchOutput : Register → InstructionMatch.Output
  | .instr_beq => .instr_beq | .instr_bne => .instr_bne
  | .instr_blt => .instr_blt | .instr_bge => .instr_bge
  | .instr_bltu => .instr_bltu | .instr_bgeu => .instr_bgeu
  | .instr_lb => .instr_lb | .instr_lh => .instr_lh
  | .instr_lw => .instr_lw | .instr_lbu => .instr_lbu
  | .instr_lhu => .instr_lhu
  | .instr_sb => .instr_sb | .instr_sh => .instr_sh | .instr_sw => .instr_sw
  | .instr_addi => .instr_addi | .instr_slti => .instr_slti
  | .instr_sltiu => .instr_sltiu | .instr_xori => .instr_xori
  | .instr_ori => .instr_ori | .instr_andi => .instr_andi
  | .instr_slli => .instr_slli | .instr_srli => .instr_srli
  | .instr_srai => .instr_srai
  | .instr_add => .instr_add | .instr_sub => .instr_sub
  | .instr_sll => .instr_sll | .instr_slt => .instr_slt
  | .instr_sltu => .instr_sltu | .instr_xor => .instr_xor
  | .instr_srl => .instr_srl | .instr_sra => .instr_sra
  | .instr_or => .instr_or | .instr_and => .instr_and
  | .instr_ecall_ebreak => .instr_ecall_ebreak | .instr_fence => .instr_fence
  | .is_slli_srli_srai => .is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      .is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_sll_srl_sra => .is_sll_srl_sra
  | .decoded_imm | .is_lui_auipc_jal |
      .is_lui_auipc_jal_jalr_addi_add_sub | .is_slti_blt_slt |
      .is_sltiu_bltu_sltu | .is_lbu_lhu_lw | .is_compare =>
      .instr_fence -- unreachable for the two match-register groups

private def summaryOutput : Register → InstructionSummary.Output
  | .is_lui_auipc_jal => .is_lui_auipc_jal
  | .is_lui_auipc_jal_jalr_addi_add_sub => .is_lui_auipc_jal_jalr_addi_add_sub
  | .is_slti_blt_slt => .is_slti_blt_slt
  | .is_sltiu_bltu_sltu => .is_sltiu_bltu_sltu
  | .is_lbu_lhu_lw => .is_lbu_lhu_lw
  | .is_compare => .is_compare
  | _ => .instr_trap -- unreachable for summary registers

def resetMatchCombiner : Composition.SignalCombiner := .vector 23 .bit
def retainedMatchCombiner : Composition.SignalCombiner := .vector 15 .bit
def ordinarySummaryCombiner : Composition.SignalCombiner := .vector 4 .bit
def resetMatchSplitter : Composition.SignalSplitter := .vector 23 .bit
def retainedMatchSplitter : Composition.SignalSplitter := .vector 15 .bit
def ordinarySummarySplitter : Composition.SignalSplitter := .vector 4 .bit
end Silean.Examples.PicoRV.Decoder.ResolveStage

namespace Silean.Examples.PicoRV.Decoder

open Silean
open Silean.Authoring

module_design ResolveStage where
  boundary (ResolveStage.ports) (naming := ResolveStage.Naming.ports)
  instances {
    pseudoInverter := Primitives.notDesign,
    triggerEnable := Primitives.andDesign,
    resetInverter := Primitives.notDesign,
    instructionMatch := InstructionMatch.cycleContract.blackboxDesign
      "PicoRVDecoderInstructionMatch" InstructionMatch.Naming.ports,
    immediate := Immediate.cycleContract.blackboxDesign
      "PicoRVDecoderImmediate" Immediate.Naming.ports,
    instructionSummary := InstructionSummary.cycleContract.blackboxDesign
      "PicoRVDecoderInstructionSummary" InstructionSummary.Naming.ports,
    resetMatchNext := Naming.SignalAdapter.combinerDesign (.vector 23 .bit),
    retainedMatchNext := Naming.SignalAdapter.combinerDesign (.vector 15 .bit),
    ordinarySummaryNext := Naming.SignalAdapter.combinerDesign (.vector 4 .bit),
    resetMatchStorage := Modules.EnabledResetRegister.design
      ResolveStage.resetMatchType ResolveStage.falseResetMatches,
    retainedMatchStorage := Modules.EnabledRegister.design ResolveStage.retainedMatchType,
    immediateStorage := Modules.EnabledRegister.design ResolveStage.immediateType,
    ordinarySummaryStorage := Modules.Register.design ResolveStage.ordinarySummaryType,
    addSubSummaryStorage := Modules.Register.design .bit,
    compareStorage := Modules.ResetRegister.design .bit false,
    immediateSelection := Modules.Mux.design ResolveStage.immediateType,
    addSubSummarySelection := Modules.Mux.design .bit,
    compareSelection := Modules.Mux.design .bit,
    resetMatchOutputs := Naming.SignalAdapter.splitterDesign (.vector 23 .bit),
    retainedMatchOutputs := Naming.SignalAdapter.splitterDesign (.vector 15 .bit),
    ordinarySummaryOutputs := Naming.SignalAdapter.splitterDesign (.vector 4 .bit),
    falseValue := Modules.Constant.design .bit false }
  wiring {
  outputs {
    .instr_trap := instructionSummary.instr_trap,
    .instr_beq := resetMatchOutputs[0],
    .instr_bne := resetMatchOutputs[1],
    .instr_blt := resetMatchOutputs[2],
    .instr_bge := resetMatchOutputs[3],
    .instr_bltu := resetMatchOutputs[4],
    .instr_bgeu := resetMatchOutputs[5],
    .instr_lb := retainedMatchOutputs[0],
    .instr_lh := retainedMatchOutputs[1],
    .instr_lw := retainedMatchOutputs[2],
    .instr_lbu := retainedMatchOutputs[3],
    .instr_lhu := retainedMatchOutputs[4],
    .instr_sb := retainedMatchOutputs[5],
    .instr_sh := retainedMatchOutputs[6],
    .instr_sw := retainedMatchOutputs[7],
    .instr_addi := resetMatchOutputs[6],
    .instr_slti := resetMatchOutputs[7],
    .instr_sltiu := resetMatchOutputs[8],
    .instr_xori := resetMatchOutputs[9],
    .instr_ori := resetMatchOutputs[10],
    .instr_andi := resetMatchOutputs[11],
    .instr_slli := retainedMatchOutputs[8],
    .instr_srli := retainedMatchOutputs[9],
    .instr_srai := retainedMatchOutputs[10],
    .instr_add := resetMatchOutputs[12],
    .instr_sub := resetMatchOutputs[13],
    .instr_sll := resetMatchOutputs[14],
    .instr_slt := resetMatchOutputs[15],
    .instr_sltu := resetMatchOutputs[16],
    .instr_xor := resetMatchOutputs[17],
    .instr_srl := resetMatchOutputs[18],
    .instr_sra := resetMatchOutputs[19],
    .instr_or := resetMatchOutputs[20],
    .instr_and := resetMatchOutputs[21],
    .instr_fence := resetMatchOutputs[22],
    .decoded_imm := immediateStorage.q,
    .is_lui_auipc_jal := ordinarySummaryOutputs[0],
    .is_slli_srli_srai := retainedMatchOutputs[12],
    .is_jalr_addi_slti_sltiu_xori_ori_andi := retainedMatchOutputs[13],
    .is_sll_srl_sra := retainedMatchOutputs[14],
    .is_lui_auipc_jal_jalr_addi_add_sub := addSubSummaryStorage.output,
    .is_slti_blt_slt := ordinarySummaryOutputs[1],
    .is_sltiu_bltu_sltu := ordinarySummaryOutputs[2],
    .is_lbu_lhu_lw := ordinarySummaryOutputs[3],
    .is_compare := compareStorage.value }
  instance (.pseudoInverter) {
    .input := input.decoder_pseudo_trigger }
  instance (.triggerEnable) {
    .left := input.decoder_trigger,
    .right := pseudoInverter.output }
  instance (.resetInverter) {
    .input := input.resetn }
  instance (.instructionMatch) {
    .word := input.mem_rdata_q,
    .instr_jalr := input.instr_jalr,
    .is_beq_bne_blt_bge_bltu_bgeu := input.is_beq_bne_blt_bge_bltu_bgeu,
    .is_lb_lh_lw_lbu_lhu := input.is_lb_lh_lw_lbu_lhu,
    .is_sb_sh_sw := input.is_sb_sh_sw,
    .is_alu_reg_imm := input.is_alu_reg_imm,
    .is_alu_reg_reg := input.is_alu_reg_reg }
  instance (.immediate) {
    .word := input.mem_rdata_q,
    .decoded_imm_j := input.decoded_imm_j,
    .instr_jal := input.instr_jal,
    .instr_lui := input.instr_lui,
    .instr_auipc := input.instr_auipc,
    .instr_jalr := input.instr_jalr,
    .is_lb_lh_lw_lbu_lhu := input.is_lb_lh_lw_lbu_lhu,
    .is_alu_reg_imm := input.is_alu_reg_imm,
    .is_beq_bne_blt_bge_bltu_bgeu := input.is_beq_bne_blt_bge_bltu_bgeu,
    .is_sb_sh_sw := input.is_sb_sh_sw }
  instance (.instructionSummary) {
    .instr_lui := input.instr_lui,
    .instr_auipc := input.instr_auipc,
    .instr_jal := input.instr_jal,
    .instr_jalr := input.instr_jalr,
    .is_beq_bne_blt_bge_bltu_bgeu := input.is_beq_bne_blt_bge_bltu_bgeu,
    .instr_beq := resetMatchOutputs[0],
    .instr_bne := resetMatchOutputs[1],
    .instr_blt := resetMatchOutputs[2],
    .instr_bge := resetMatchOutputs[3],
    .instr_bltu := resetMatchOutputs[4],
    .instr_bgeu := resetMatchOutputs[5],
    .instr_lb := retainedMatchOutputs[0],
    .instr_lh := retainedMatchOutputs[1],
    .instr_lw := retainedMatchOutputs[2],
    .instr_lbu := retainedMatchOutputs[3],
    .instr_lhu := retainedMatchOutputs[4],
    .instr_sb := retainedMatchOutputs[5],
    .instr_sh := retainedMatchOutputs[6],
    .instr_sw := retainedMatchOutputs[7],
    .instr_addi := resetMatchOutputs[6],
    .instr_slti := resetMatchOutputs[7],
    .instr_sltiu := resetMatchOutputs[8],
    .instr_xori := resetMatchOutputs[9],
    .instr_ori := resetMatchOutputs[10],
    .instr_andi := resetMatchOutputs[11],
    .instr_slli := retainedMatchOutputs[8],
    .instr_srli := retainedMatchOutputs[9],
    .instr_srai := retainedMatchOutputs[10],
    .instr_add := resetMatchOutputs[12],
    .instr_sub := resetMatchOutputs[13],
    .instr_sll := resetMatchOutputs[14],
    .instr_slt := resetMatchOutputs[15],
    .instr_sltu := resetMatchOutputs[16],
    .instr_xor := resetMatchOutputs[17],
    .instr_srl := resetMatchOutputs[18],
    .instr_sra := resetMatchOutputs[19],
    .instr_or := resetMatchOutputs[20],
    .instr_and := resetMatchOutputs[21],
    .instr_ecall_ebreak := retainedMatchOutputs[11],
    .instr_fence := resetMatchOutputs[22] }
  instance (.resetMatchNext) {
    index := from (SignalSource.castType
      (InstructionMatch.output_signalType _)
      (c.instanceOutput .instructionMatch
        (ResolveStage.matchOutput (ResolveStage.resetMatchRegister index)))) }
  instance (.retainedMatchNext) {
    index := from (SignalSource.castType
      (InstructionMatch.output_signalType _)
      (c.instanceOutput .instructionMatch
        (ResolveStage.matchOutput (ResolveStage.retainedMatchRegister index)))) }
  instance (.ordinarySummaryNext) {
    index := from (SignalSource.castType
      (InstructionSummary.output_signalType _)
      (c.instanceOutput .instructionSummary
        (ResolveStage.summaryOutput (ResolveStage.ordinarySummaryRegister index)))) }
  instance (.resetMatchStorage) {
    .value := resetMatchNext.value,
    .enable := triggerEnable.output,
    .reset := resetInverter.output }
  instance (.retainedMatchStorage) {
    .data := retainedMatchNext.value,
    .enable := triggerEnable.output }
  instance (.immediateSelection) {
    .select := immediate.valid,
    .whenFalse := immediateStorage.q,
    .whenTrue := immediate.value }
  instance (.immediateStorage) {
    .data := immediateSelection.result,
    .enable := triggerEnable.output }
  instance (.ordinarySummaryStorage) {
    .input := ordinarySummaryNext.value }
  instance (.addSubSummarySelection) {
    .select := triggerEnable.output,
    .whenFalse := instructionSummary.is_lui_auipc_jal_jalr_addi_add_sub,
    .whenTrue := falseValue.output }
  instance (.addSubSummaryStorage) {
    .input := addSubSummarySelection.result }
  instance (.compareSelection) {
    .select := triggerEnable.output,
    .whenFalse := instructionSummary.is_compare,
    .whenTrue := falseValue.output }
  instance (.compareStorage) {
    .value := compareSelection.result,
    .reset := resetInverter.output }
  instance (.resetMatchOutputs) {
    .value := resetMatchStorage.value }
  instance (.retainedMatchOutputs) {
    .value := retainedMatchStorage.q }
  instance (.ordinarySummaryOutputs) {
    .value := ordinarySummaryStorage.output }
  instance (.falseValue) {}
  }

end Silean.Examples.PicoRV.Decoder
