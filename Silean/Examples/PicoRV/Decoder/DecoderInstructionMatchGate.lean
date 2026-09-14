import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.And

namespace Silean.Examples.PicoRV.Decoder.InstructionMatch.MatchGate

open Silean
open Silean.Authoring

/-! One exact instruction predicate is the conjunction of its broad opcode
class, its field match, and an optional qualifier. Keeping this two-gate detail
behind a uniform boundary makes the instruction matcher hierarchy readable. -/

module_ports ports where
  input broad : .bit,
  input field : .bit,
  input qualifier : .bit,
  output result : .bit

def outputRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := fun
    | .result => (inputs .broad && inputs .field) && inputs .qualifier

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .result = ((inputs .broad && inputs .field) && inputs .qualifier) := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, outputRule]
  constructor
  · intro equal
    exact congrFun equal .result
  · intro equal
    funext output
    cases output
    exact equal

module_design Structure (name := "PicoRVDecoderInstructionPredicate") where
  boundary (ports) (naming := Naming.ports)
  instances {
    classAndField := Primitives.andDesign,
    qualifiedResult := Primitives.andDesign }
  wiring {
  outputs { .result := qualifiedResult.output }
  instance (.classAndField) {
    .left := input.broad,
    .right := input.field }
  instance (.qualifiedResult) {
    .left := classAndField.output,
    .right := input.qualifier }
  }

end Silean.Examples.PicoRV.Decoder.InstructionMatch.MatchGate
