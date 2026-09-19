import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.CircuitDescription
import Silean.Authoring.CircuitLogic
import PicoRV.Decoder.Internal.DecoderInstructionMatchGateStructure

namespace PicoRV.Decoder.InstructionMatch.MatchGate

open Silean
open Silean.Authoring

/-! One exact instruction predicate is the conjunction of its broad opcode
class, its field match, and an optional qualifier. Keeping this two-gate detail
behind a uniform boundary makes the instruction matcher hierarchy readable. -/

/-! ## Authored hardware -/

namespace Description

open Silean.Authoring.CircuitDescription
open scoped Silean.Authoring.CircuitLogic

noncomputable def construction : Builder Unit := do
  let broad ← input "broad" .bit
  let field ← input "field" .bit
  let qualifier ← input "qualifier" .bit
  output "result" (← (← broad &&& field) &&& qualifier)

noncomputable def description : Description := build construction

end Description

/-! ## Placement -/

noncomputable def place (broad field qualifier : Authoring.CircuitDescription.Net .bit) :
    Authoring.CircuitDescription.Builder (Authoring.CircuitDescription.Net .bit) := do
  let child ← Authoring.CircuitDescription.placeIndexed "instruction_match_gate"
    Structure.design fun
      | .broad => broad
      | .field => field
      | .qualifier => qualifier
  pure (child .result)

noncomputable def placeNamed (name : Naming.SourceName)
    (broad field qualifier : Authoring.CircuitDescription.Net .bit) :
    Authoring.CircuitDescription.Builder (Authoring.CircuitDescription.Net .bit) := do
  let child ← Authoring.CircuitDescription.placeNamed name Structure.design fun
    | .broad => broad
    | .field => field
    | .qualifier => qualifier
  pure (child .result)

attribute [circuit_description] place placeNamed

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := fun
    | .result => (inputs .broad && inputs .field) && inputs .qualifier

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .result = ((inputs .broad && inputs .field) && inputs .qualifier) := by
  simp [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule]
  constructor
  · intro equal
    exact congrFun equal .result
  · intro equal
    funext output
    cases output
    exact equal

end PicoRV.Decoder.InstructionMatch.MatchGate
