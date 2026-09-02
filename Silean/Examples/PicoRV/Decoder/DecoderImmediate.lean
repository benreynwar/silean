import Silean.Examples.PicoRV.Decoder.DecoderTypes
import Silean.Composition.SignalLayout
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation

namespace Silean.Examples.PicoRV.Decoder.Immediate

open Silean
open Silean.Examples.PicoRV.Decoder

/-! Combinational immediate selection for the configured PicoRV32 decoder.
The Lean behavior is naturally an `Option Word`: no selected instruction class
means that the resolve stage must retain its existing immediate. The hardware
boundary exposes this as `valid` plus `value`; the value is zero when invalid
and must not be consumed. Selection order matches the source `case (1'b1)`. -/

inductive Input
  | word | decoded_imm_j
  | instr_jal | instr_lui | instr_auipc | instr_jalr
  | is_lb_lh_lw_lbu_lhu | is_alu_reg_imm
  | is_beq_bne_blt_bge_bltu_bgeu | is_sb_sh_sw
deriving Enumeration

inductive Output | valid | value
deriving Enumeration

def inputType : Input → SignalType
  | .word | .decoded_imm_j => .vector 32 .bit
  | _ => .bit

def outputType : Output → SignalType
  | .value => .vector 32 .bit
  | .valid => .bit

@[reducible] def inputMap : SignalMap := EnumeratedMap.of Input inputType
@[reducible] def outputMap : SignalMap := EnumeratedMap.of Output outputType
@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

structure Inputs where
  word : Word
  decoded_imm_j : Word
  instr_jal : Bool
  instr_lui : Bool
  instr_auipc : Bool
  instr_jalr : Bool
  is_lb_lh_lw_lbu_lhu : Bool
  is_alu_reg_imm : Bool
  is_beq_bne_blt_bge_bltu_bgeu : Bool
  is_sb_sh_sw : Bool

def valuesOf (inputs : inputMap.Values) : Inputs where
  word := inputs .word
  decoded_imm_j := inputs .decoded_imm_j
  instr_jal := inputs .instr_jal
  instr_lui := inputs .instr_lui
  instr_auipc := inputs .instr_auipc
  instr_jalr := inputs .instr_jalr
  is_lb_lh_lw_lbu_lhu := inputs .is_lb_lh_lw_lbu_lhu
  is_alu_reg_imm := inputs .is_alu_reg_imm
  is_beq_bne_blt_bge_bltu_bgeu := inputs .is_beq_bne_blt_bge_bltu_bgeu
  is_sb_sh_sw := inputs .is_sb_sh_sw

def evaluate (inputs : Inputs) : Option Word :=
  if inputs.instr_jal then some inputs.decoded_imm_j
  else if inputs.instr_lui || inputs.instr_auipc then some (immediateU inputs.word)
  else if inputs.instr_jalr || inputs.is_lb_lh_lw_lbu_lhu || inputs.is_alu_reg_imm then
    some (immediateI inputs.word)
  else if inputs.is_beq_bne_blt_bge_bltu_bgeu then some (immediateB inputs.word)
  else if inputs.is_sb_sh_sw then some (immediateS inputs.word)
  else none

def outputValues (inputs : Inputs) : outputMap.Values
  | .valid => (evaluate inputs).isSome
  | .value => (evaluate inputs).getD (wordOfNat 0)

inductive Rule | apply
deriving Enumeration

def outputRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap
    { inputTypes := .ofList inputMap.types,
      outputTypes := .ofList outputMap.types } where
  readsInputs := inputMap.allSelection
  writesOutputs := outputMap.allSelection
  target := fun selected _ => outputMap.allSelection.project
    (outputValues (valuesOf (inputMap.unpack selected)))

@[reducible] def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by
    change outputMap.allSelection.labels.Perm outputMap.labels.values
    rw [SignalMap.allSelection_labels]

@[simp] theorem outputRule_reads (input : Input) :
    input ∈ outputRule.readsInputs.labels := by
  change input ∈ inputMap.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact (inputMap.labels.locate input).mem

@[simp] theorem outputRule_writes (output : Output) :
    output ∈ outputRule.writesOutputs.labels := by
  change output ∈ outputMap.allSelection.labels
  rw [SignalMap.allSelection_labels]
  exact (outputMap.labels.locate output).mem

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs = outputValues (valuesOf inputs) := by
  change outputMap.allSelection.Matches outputs
      (outputMap.allSelection.project
        (outputValues (valuesOf (inputMap.unpack
          (inputMap.allSelection.project inputs))))) ↔ _
  rw [inputMap.unpack_project, SignalSelection.allSelection_matches_project_iff]

end Silean.Examples.PicoRV.Decoder.Immediate
