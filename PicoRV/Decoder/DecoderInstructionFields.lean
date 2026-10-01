import PicoRV.Decoder.DecoderInstructionMatch
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

/-! # Shared instruction fields

This decoder child exposes the field comparisons reused by the exact
instruction matcher.
-/

namespace PicoRV.Decoder.InstructionFields

open Silean
open Silean.Authoring
open InstructionMatch

module_ports ports where
  input word : .vector 32 .bit,
  output funct3_0 : .bit,
  output funct3_1 : .bit,
  output funct3_2 : .bit,
  output funct3_3 : .bit,
  output funct3_4 : .bit,
  output funct3_5 : .bit,
  output funct3_6 : .bit,
  output funct3_7 : .bit,
  output funct7_zero : .bit,
  output funct7_alternate : .bit,
  output opcode_system : .bit,
  output opcode_fence : .bit,
  output system_middle_zero : .bit,
  output system_outer_zero : .bit,
  output true_value : .bit

def outputValues (word : Word) : ports.outputs.Values
  | .funct3_0 => decide (funct3 word = 0)
  | .funct3_1 => decide (funct3 word = 1)
  | .funct3_2 => decide (funct3 word = 2)
  | .funct3_3 => decide (funct3 word = 3)
  | .funct3_4 => decide (funct3 word = 4)
  | .funct3_5 => decide (funct3 word = 5)
  | .funct3_6 => decide (funct3 word = 6)
  | .funct3_7 => decide (funct3 word = 7)
  | .funct7_zero => decide (funct7 word = 0)
  | .funct7_alternate => decide (funct7 word = 0x20)
  | .opcode_system => decide (opcode word = 0x73)
  | .opcode_fence => decide (opcode word = 0x0f)
  | .system_middle_zero => decide (field word 21 11 = 0)
  | .system_outer_zero => decide (field word 7 13 = 0)
  | .true_value => true

def outputRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := outputValues (inputs .word)

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔ outputs = outputValues (inputs .word) := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, outputRule]

/-- Every allowed step exposes exactly the predicates decoded from `word`. -/
theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs = outputValues (step.inputs .word) :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

end PicoRV.Decoder.InstructionFields
