import Silean.Contracts.Cycle.CycleImplementation
import Silean.Authoring.CircuitDescription
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.NotPrimitive

namespace Silean.Primitives

open Silean

inductive NotRule | apply
deriving Enumeration

def notOutputRule : Contracts.Cycle.CycleOutputRule not.ports emptySignalMap where
  readsInputs := .all not.ports.inputs
  writesOutputs := .all not.ports.outputs
  target inputs _ := fun | .output => !(inputs .input)

def notCycleContract : Contracts.Cycle.ModuleCycleContract not.ports where
  state := emptySignalMap
  RuleName := NotRule
  ruleNames := inferInstance
  outputRule | .apply => notOutputRule
  stateRule := Contracts.Cycle.CycleStateRule.empty not.ports
  outputCoverage := by rfl

@[simp] theorem notOutputRule_holds_iff
    (inputs : not.ports.inputs.Values)
    (state : notCycleContract.state.Values)
    (outputs : not.ports.outputs.Values) :
    notOutputRule.Holds inputs state outputs ↔ outputs .output = !inputs .input := by
  simp only [notOutputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

private def notStateCorresponds (_ : notCycleContract.state.Values)
    (_ : (ModuleStructure.primitive not).State) : Prop := True

private theorem notImplements : Contracts.Cycle.ImplementsSolutions (.primitive not) notCycleContract
    notStateCorresponds := by
  intro contractState hierStep corresponds satisfies
  cases hierStep with
  | mk inputs structuralState outputs nextState =>
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change notOutputRule.Holds inputs contractState outputs
    change outputs = not.outputValues inputs structuralState ∧
      nextState = not.nextStateValues inputs structuralState at satisfies
    rw [satisfies.1]
    exact SignalGroup.matches_project _ _
  · rfl

def notCertified : Contracts.Cycle.ModuleCycleCertified not.ports where
  moduleStructure := .primitive not
  cycleContract := notCycleContract
  certification := {
    stateCorresponds := notStateCorresponds
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
    hasStructuralResult := Primitive.hasSolution not
    structuralResultUnique := Primitive.hasAtMostOneSolution not
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp notImplements }

end Silean.Primitives

namespace Silean.Primitives.Not

open Silean.Naming
open Silean.Authoring.CircuitDescription

/-- Place a one-bit inverter under a caller-chosen instance name. -/
def placeNamed (name : Silean.Naming.SourceName)
    (input : Net .bit) : Builder (Net .bit) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    Primitives.notDesign (fun _ => input)
  pure (child .output)

/-- Place a one-bit inverter in a circuit description. -/
def place (input : Net .bit) : Builder (Net .bit) := do
  let child ← Authoring.CircuitDescription.placeIndexed "not"
    Primitives.notDesign (fun _ => input)
  pure (child .output)

end Silean.Primitives.Not
