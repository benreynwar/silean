import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatch
import Silean.Composition.SignalLayout
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation

namespace Silean.Examples.PicoRV.Decoder.InstructionSummary

open Silean
open Silean.Examples.PicoRV.Decoder

/-! Combinational views of the decoder's current, pre-edge instruction flags.
The six registered summaries in `picorv32.v` are computed every cycle from
these values. `instr_trap` is the configured (`CATCH_ILLINSN = 1`) continuous
illegal-instruction result. Trigger gating and registers belong to the parent
resolve stage, so this boundary deliberately has neither. -/

inductive Input
  | instr_lui | instr_auipc | instr_jal | instr_jalr
  | is_beq_bne_blt_bge_bltu_bgeu
  | instr_beq | instr_bne | instr_blt | instr_bge | instr_bltu | instr_bgeu
  | instr_lb | instr_lh | instr_lw | instr_lbu | instr_lhu
  | instr_sb | instr_sh | instr_sw
  | instr_addi | instr_slti | instr_sltiu | instr_xori | instr_ori | instr_andi
  | instr_slli | instr_srli | instr_srai
  | instr_add | instr_sub | instr_sll | instr_slt | instr_sltu
  | instr_xor | instr_srl | instr_sra | instr_or | instr_and
  | instr_ecall_ebreak | instr_fence
deriving Enumeration

inductive Output
  | instr_trap
  | is_lui_auipc_jal
  | is_lui_auipc_jal_jalr_addi_add_sub
  | is_slti_blt_slt | is_sltiu_bltu_sltu | is_lbu_lhu_lw | is_compare
deriving Enumeration

@[reducible] def inputMap : SignalMap := EnumeratedMap.of Input fun _ => .bit
@[reducible] def outputMap : SignalMap := EnumeratedMap.of Output fun _ => .bit
@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

structure Inputs where
  instr_lui : Bool
  instr_auipc : Bool
  instr_jal : Bool
  instr_jalr : Bool
  is_beq_bne_blt_bge_bltu_bgeu : Bool
  matched : InstructionMatch.outputMap.Values

def matchedValues (inputs : inputMap.Values) : InstructionMatch.outputMap.Values
  | .instr_beq => inputs .instr_beq | .instr_bne => inputs .instr_bne
  | .instr_blt => inputs .instr_blt | .instr_bge => inputs .instr_bge
  | .instr_bltu => inputs .instr_bltu | .instr_bgeu => inputs .instr_bgeu
  | .instr_lb => inputs .instr_lb | .instr_lh => inputs .instr_lh
  | .instr_lw => inputs .instr_lw | .instr_lbu => inputs .instr_lbu
  | .instr_lhu => inputs .instr_lhu
  | .instr_sb => inputs .instr_sb | .instr_sh => inputs .instr_sh
  | .instr_sw => inputs .instr_sw
  | .instr_addi => inputs .instr_addi | .instr_slti => inputs .instr_slti
  | .instr_sltiu => inputs .instr_sltiu | .instr_xori => inputs .instr_xori
  | .instr_ori => inputs .instr_ori | .instr_andi => inputs .instr_andi
  | .instr_slli => inputs .instr_slli | .instr_srli => inputs .instr_srli
  | .instr_srai => inputs .instr_srai
  | .instr_add => inputs .instr_add | .instr_sub => inputs .instr_sub
  | .instr_sll => inputs .instr_sll | .instr_slt => inputs .instr_slt
  | .instr_sltu => inputs .instr_sltu | .instr_xor => inputs .instr_xor
  | .instr_srl => inputs .instr_srl | .instr_sra => inputs .instr_sra
  | .instr_or => inputs .instr_or | .instr_and => inputs .instr_and
  | .instr_ecall_ebreak => inputs .instr_ecall_ebreak
  | .instr_fence => inputs .instr_fence
  | .is_slli_srli_srai | .is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_sll_srl_sra => false

def valuesOf (inputs : inputMap.Values) : Inputs where
  instr_lui := inputs .instr_lui
  instr_auipc := inputs .instr_auipc
  instr_jal := inputs .instr_jal
  instr_jalr := inputs .instr_jalr
  is_beq_bne_blt_bge_bltu_bgeu := inputs .is_beq_bne_blt_bge_bltu_bgeu
  matched := matchedValues inputs

def recognized (inputs : Inputs) : Bool := boolOr [
  inputs.instr_lui, inputs.instr_auipc, inputs.instr_jal, inputs.instr_jalr,
  inputs.matched .instr_beq, inputs.matched .instr_bne,
  inputs.matched .instr_blt, inputs.matched .instr_bge,
  inputs.matched .instr_bltu, inputs.matched .instr_bgeu,
  inputs.matched .instr_lb, inputs.matched .instr_lh, inputs.matched .instr_lw,
  inputs.matched .instr_lbu, inputs.matched .instr_lhu,
  inputs.matched .instr_sb, inputs.matched .instr_sh, inputs.matched .instr_sw,
  inputs.matched .instr_addi, inputs.matched .instr_slti,
  inputs.matched .instr_sltiu, inputs.matched .instr_xori,
  inputs.matched .instr_ori, inputs.matched .instr_andi,
  inputs.matched .instr_slli, inputs.matched .instr_srli,
  inputs.matched .instr_srai, inputs.matched .instr_add,
  inputs.matched .instr_sub, inputs.matched .instr_sll,
  inputs.matched .instr_slt, inputs.matched .instr_sltu,
  inputs.matched .instr_xor, inputs.matched .instr_srl,
  inputs.matched .instr_sra, inputs.matched .instr_or,
  inputs.matched .instr_and, inputs.matched .instr_ecall_ebreak,
  inputs.matched .instr_fence]

def outputValues (inputs : Inputs) : Output → Bool
  | .instr_trap => !(recognized inputs)
  | .is_lui_auipc_jal => boolOr [inputs.instr_lui, inputs.instr_auipc, inputs.instr_jal]
  | .is_lui_auipc_jal_jalr_addi_add_sub => boolOr [inputs.instr_lui,
      inputs.instr_auipc, inputs.instr_jal, inputs.instr_jalr,
      inputs.matched .instr_addi, inputs.matched .instr_add, inputs.matched .instr_sub]
  | .is_slti_blt_slt => boolOr [inputs.matched .instr_slti,
      inputs.matched .instr_blt, inputs.matched .instr_slt]
  | .is_sltiu_bltu_sltu => boolOr [inputs.matched .instr_sltiu,
      inputs.matched .instr_bltu, inputs.matched .instr_sltu]
  | .is_lbu_lhu_lw => boolOr [inputs.matched .instr_lbu,
      inputs.matched .instr_lhu, inputs.matched .instr_lw]
  | .is_compare => boolOr [inputs.is_beq_bne_blt_bge_bltu_bgeu,
      inputs.matched .instr_slti, inputs.matched .instr_slt,
      inputs.matched .instr_sltiu, inputs.matched .instr_sltu]

private def trapInputLabels : List Input := [
  .instr_lui, .instr_auipc, .instr_jal, .instr_jalr,
  .instr_beq, .instr_bne, .instr_blt, .instr_bge, .instr_bltu, .instr_bgeu,
  .instr_lb, .instr_lh, .instr_lw, .instr_lbu, .instr_lhu,
  .instr_sb, .instr_sh, .instr_sw,
  .instr_addi, .instr_slti, .instr_sltiu, .instr_xori, .instr_ori, .instr_andi,
  .instr_slli, .instr_srli, .instr_srai,
  .instr_add, .instr_sub, .instr_sll, .instr_slt, .instr_sltu,
  .instr_xor, .instr_srl, .instr_sra, .instr_or, .instr_and,
  .instr_ecall_ebreak, .instr_fence]

private def summaryOutputLabels : List Output := [
  .is_lui_auipc_jal, .is_lui_auipc_jal_jalr_addi_add_sub,
  .is_slti_blt_slt, .is_sltiu_bltu_sltu, .is_lbu_lhu_lw, .is_compare]

inductive Rule | trap | summaries
deriving Enumeration

def trapOutputRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap
    { inputTypes := .ofList (trapInputLabels.map inputMap.signalType),
      outputTypes := .cons .bit .nil } where
  readsInputs := inputMap.selectionFrom trapInputLabels
  writesOutputs := outputMap.select .instr_trap
  target := fun selected _ =>
    (!(recognized (valuesOf (inputMap.unpackFrom trapInputLabels selected))), ())

def summariesOutputRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap
    { inputTypes := .ofList inputMap.types,
      outputTypes := .ofList (summaryOutputLabels.map outputMap.signalType) } where
  readsInputs := inputMap.allSelection
  writesOutputs := outputMap.selectionFrom summaryOutputLabels
  target := fun selected _ => outputMap.selectionFrom summaryOutputLabels |>.project
    (outputValues (valuesOf (inputMap.unpack selected)))

@[reducible] def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .trap => ⟨_, trapOutputRule⟩
    | .summaries => ⟨_, summariesOutputRule⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem trapOutputRule_reads (input : Input) :
  input ∈ trapOutputRule.readsInputs.labels ↔
      input ≠ .is_beq_bne_blt_bge_bltu_bgeu := by
  change input ∈ trapInputLabels ↔ _
  cases input <;> simp [trapInputLabels]

@[simp] theorem summariesOutputRule_reads (input : Input) :
    input ∈ summariesOutputRule.readsInputs.labels := by
  change input ∈ inputMap.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact (inputMap.labels.locate input).mem

@[simp] theorem trapOutputRule_writes (output : Output) :
    output ∈ trapOutputRule.writesOutputs.labels ↔ output = .instr_trap := by
  cases output <;> simp [trapOutputRule, SignalMap.select, SignalSelection.labels]

@[simp] theorem summariesOutputRule_writes (output : Output) :
    output ∈ summariesOutputRule.writesOutputs.labels ↔ output ≠ .instr_trap := by
  change output ∈ summaryOutputLabels ↔ _
  cases output <;> simp [summaryOutputLabels]

@[simp] theorem trapOutputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    trapOutputRule.Holds inputs state outputs ↔
      outputs .instr_trap = outputValues (valuesOf inputs) .instr_trap := by
  let selected := inputMap.unpackFrom trapInputLabels
    (inputMap.selectionFrom trapInputLabels |>.project inputs)
  have selected_eq (input : Input) (member : input ∈ trapInputLabels) :
      selected input = inputs input := by
    exact inputMap.unpackFrom_project_eq_of_mem trapInputLabels inputs input member
  have recognized_eq : recognized (valuesOf selected) = recognized (valuesOf inputs) := by
    simp [recognized, valuesOf, matchedValues, selected_eq, trapInputLabels]
  simp only [trapOutputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalSelection.Matches, SignalMap.select]
  change outputs .instr_trap = !recognized (valuesOf selected) ∧ True ↔ _
  rw [recognized_eq]
  simp [outputValues]

end Silean.Examples.PicoRV.Decoder.InstructionSummary
