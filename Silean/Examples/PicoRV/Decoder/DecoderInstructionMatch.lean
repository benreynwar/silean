import Silean.Examples.PicoRV.Decoder.DecoderTypes
import Silean.Foundation.SignalLayout
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation

namespace Silean.Examples.PicoRV.Decoder.InstructionMatch

open Silean
open Silean.Examples.PicoRV.Decoder

/-! Exact combinational instruction matching for the configured RV32I subset.
It refines the five broad opcode classes captured on the preceding cycle using
the current instruction's `funct3` and `funct7` fields. It contains no trigger,
register, reset, or update-priority behavior. -/

inductive Input
  | word | instr_jalr
  | is_beq_bne_blt_bge_bltu_bgeu | is_lb_lh_lw_lbu_lhu | is_sb_sh_sw
  | is_alu_reg_imm | is_alu_reg_reg
deriving Enumeration

inductive Output
  | instr_beq | instr_bne | instr_blt | instr_bge | instr_bltu | instr_bgeu
  | instr_lb | instr_lh | instr_lw | instr_lbu | instr_lhu
  | instr_sb | instr_sh | instr_sw
  | instr_addi | instr_slti | instr_sltiu | instr_xori | instr_ori | instr_andi
  | instr_slli | instr_srli | instr_srai
  | instr_add | instr_sub | instr_sll | instr_slt | instr_sltu
  | instr_xor | instr_srl | instr_sra | instr_or | instr_and
  | instr_ecall_ebreak | instr_fence
  | is_slli_srli_srai | is_jalr_addi_slti_sltiu_xori_ori_andi | is_sll_srl_sra
deriving Enumeration

def inputType : Input → SignalType
  | .word => .vector 32 .bit
  | _ => .bit

@[reducible] def inputMap : SignalMap := EnumeratedMap.of Input inputType
@[reducible] def outputMap : SignalMap := EnumeratedMap.of Output fun _ => .bit
@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

structure Inputs where
  word : Word
  instr_jalr : Bool
  is_beq_bne_blt_bge_bltu_bgeu : Bool
  is_lb_lh_lw_lbu_lhu : Bool
  is_sb_sh_sw : Bool
  is_alu_reg_imm : Bool
  is_alu_reg_reg : Bool

def valuesOf (inputs : inputMap.Values) : Inputs where
  word := inputs .word
  instr_jalr := inputs .instr_jalr
  is_beq_bne_blt_bge_bltu_bgeu := inputs .is_beq_bne_blt_bge_bltu_bgeu
  is_lb_lh_lw_lbu_lhu := inputs .is_lb_lh_lw_lbu_lhu
  is_sb_sh_sw := inputs .is_sb_sh_sw
  is_alu_reg_imm := inputs .is_alu_reg_imm
  is_alu_reg_reg := inputs .is_alu_reg_reg

def matches3 (inputs : Inputs) (enabled : Bool) (code : Nat) : Bool :=
  enabled && decide (funct3 inputs.word = code)

def matches37 (inputs : Inputs) (enabled : Bool) (code3 code7 : Nat) : Bool :=
  enabled && decide (funct3 inputs.word = code3 ∧ funct7 inputs.word = code7)

def outputValues (inputs : Inputs) : Output → Bool
  | .instr_beq => matches3 inputs inputs.is_beq_bne_blt_bge_bltu_bgeu 0
  | .instr_bne => matches3 inputs inputs.is_beq_bne_blt_bge_bltu_bgeu 1
  | .instr_blt => matches3 inputs inputs.is_beq_bne_blt_bge_bltu_bgeu 4
  | .instr_bge => matches3 inputs inputs.is_beq_bne_blt_bge_bltu_bgeu 5
  | .instr_bltu => matches3 inputs inputs.is_beq_bne_blt_bge_bltu_bgeu 6
  | .instr_bgeu => matches3 inputs inputs.is_beq_bne_blt_bge_bltu_bgeu 7
  | .instr_lb => matches3 inputs inputs.is_lb_lh_lw_lbu_lhu 0
  | .instr_lh => matches3 inputs inputs.is_lb_lh_lw_lbu_lhu 1
  | .instr_lw => matches3 inputs inputs.is_lb_lh_lw_lbu_lhu 2
  | .instr_lbu => matches3 inputs inputs.is_lb_lh_lw_lbu_lhu 4
  | .instr_lhu => matches3 inputs inputs.is_lb_lh_lw_lbu_lhu 5
  | .instr_sb => matches3 inputs inputs.is_sb_sh_sw 0
  | .instr_sh => matches3 inputs inputs.is_sb_sh_sw 1
  | .instr_sw => matches3 inputs inputs.is_sb_sh_sw 2
  | .instr_addi => matches3 inputs inputs.is_alu_reg_imm 0
  | .instr_slti => matches3 inputs inputs.is_alu_reg_imm 2
  | .instr_sltiu => matches3 inputs inputs.is_alu_reg_imm 3
  | .instr_xori => matches3 inputs inputs.is_alu_reg_imm 4
  | .instr_ori => matches3 inputs inputs.is_alu_reg_imm 6
  | .instr_andi => matches3 inputs inputs.is_alu_reg_imm 7
  | .instr_slli => matches37 inputs inputs.is_alu_reg_imm 1 0
  | .instr_srli => matches37 inputs inputs.is_alu_reg_imm 5 0
  | .instr_srai => matches37 inputs inputs.is_alu_reg_imm 5 0x20
  | .instr_add => matches37 inputs inputs.is_alu_reg_reg 0 0
  | .instr_sub => matches37 inputs inputs.is_alu_reg_reg 0 0x20
  | .instr_sll => matches37 inputs inputs.is_alu_reg_reg 1 0
  | .instr_slt => matches37 inputs inputs.is_alu_reg_reg 2 0
  | .instr_sltu => matches37 inputs inputs.is_alu_reg_reg 3 0
  | .instr_xor => matches37 inputs inputs.is_alu_reg_reg 4 0
  | .instr_srl => matches37 inputs inputs.is_alu_reg_reg 5 0
  | .instr_sra => matches37 inputs inputs.is_alu_reg_reg 5 0x20
  | .instr_or => matches37 inputs inputs.is_alu_reg_reg 6 0
  | .instr_and => matches37 inputs inputs.is_alu_reg_reg 7 0
  | .instr_ecall_ebreak => decide (opcode inputs.word = 0x73 ∧
      field inputs.word 21 11 = 0 ∧ field inputs.word 7 13 = 0)
  | .instr_fence => decide (opcode inputs.word = 0x0f ∧ funct3 inputs.word = 0)
  | .is_slli_srli_srai => inputs.is_alu_reg_imm && boolOr [
      decide (funct3 inputs.word = 1 ∧ funct7 inputs.word = 0),
      decide (funct3 inputs.word = 5 ∧ funct7 inputs.word = 0),
      decide (funct3 inputs.word = 5 ∧ funct7 inputs.word = 0x20)]
  | .is_jalr_addi_slti_sltiu_xori_ori_andi => inputs.instr_jalr ||
      (inputs.is_alu_reg_imm && decide (funct3 inputs.word = 0 ∨
        funct3 inputs.word = 2 ∨ funct3 inputs.word = 3 ∨
        funct3 inputs.word = 4 ∨ funct3 inputs.word = 6 ∨ funct3 inputs.word = 7))
  | .is_sll_srl_sra => inputs.is_alu_reg_reg && boolOr [
      decide (funct3 inputs.word = 1 ∧ funct7 inputs.word = 0),
      decide (funct3 inputs.word = 5 ∧ funct7 inputs.word = 0),
      decide (funct3 inputs.word = 5 ∧ funct7 inputs.word = 0x20)]

inductive Rule | apply
deriving Enumeration

def outputRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := outputValues (valuesOf inputs)

@[reducible] def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => outputRule
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by
    change outputMap.labels.values.Perm outputMap.labels.values
    rfl

@[simp] theorem outputRule_reads (input : Input) :
    input ∈ outputRule.readsInputs.labels := by
  change input ∈ (SignalGroup.all inputMap).labels
  rw [SignalGroup.all_labels]
  exact (inputMap.labels.locate input).mem

@[simp] theorem outputRule_writes (output : Output) :
    output ∈ outputRule.writesOutputs.labels := by
  change output ∈ (SignalGroup.all outputMap).labels
  rw [SignalGroup.all_labels]
  exact (outputMap.labels.locate output).mem

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs = outputValues (valuesOf inputs) := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, outputRule]

end Silean.Examples.PicoRV.Decoder.InstructionMatch
