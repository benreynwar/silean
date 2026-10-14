import Silean.Contracts.Cycle.CycleImplementation
import Silean.Authoring.CircuitDescription
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.EqPrimitive

namespace Silean.Primitives

open Silean

inductive EqRule | apply
deriving Enumeration
def eqOutputRule : Contracts.Cycle.CycleOutputRule eq.ports emptySignalMap where
  readsInputs := .all eq.ports.inputs
  writesOutputs := .all eq.ports.outputs
  target inputs _ := fun
    | .output => (inputs .left && inputs .right) || (!inputs .left && !inputs .right)
def eqCycleContract : Contracts.Cycle.ModuleCycleContract eq.ports where
  state := emptySignalMap
  RuleName := EqRule
  ruleNames := inferInstance
  outputRule | .apply => eqOutputRule
  stateRule := Contracts.Cycle.CycleStateRule.empty eq.ports
  outputCoverage := by rfl

@[simp] theorem eqOutputRule_holds_iff
    (inputs : eq.ports.inputs.Values)
    (state : eqCycleContract.state.Values)
    (outputs : eq.ports.outputs.Values) :
    eqOutputRule.Holds inputs state outputs ↔
      outputs .output =
        ((inputs .left && inputs .right) ||
          (!inputs .left && !inputs .right)) := by
  simp only [eqOutputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

private def eqStateCorresponds (_ : eqCycleContract.state.Values)
    (_ : (ModuleStructure.primitive eq).State) : Prop := True

private theorem eqImplements : Contracts.Cycle.ImplementsSolutions (.primitive eq) eqCycleContract
    eqStateCorresponds := by
  intro contractState hierStep corresponds satisfies
  cases hierStep with
  | mk inputs structuralState outputs nextState =>
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change eqOutputRule.Holds inputs contractState outputs
    change outputs = eq.outputValues inputs structuralState ∧
      nextState = eq.nextStateValues inputs structuralState at satisfies
    rw [satisfies.1]
    exact SignalGroup.matches_project _ _
  · rfl

def eqCertified : Contracts.Cycle.ModuleCycleCertified eq.ports where
  moduleStructure := .primitive eq
  cycleContract := eqCycleContract
  certification := {
    structural := eq.structuralCertification,
    stateCorresponds := eqStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp eqImplements }
end Silean.Primitives

namespace Silean.Primitives.Eq

open Silean.Authoring.CircuitDescription

/-- Place a one-bit equality comparator under a caller-chosen instance name. -/
def placeNamed (name : Silean.Naming.SourceName)
    (left right : Net .bit) : Builder (Net .bit) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    Primitives.eqDesign fun
      | .left => left
      | .right => right
  pure (child .output)

/-- Place a one-bit equality comparator in a circuit description. -/
def place (left right : Net .bit) : Builder (Net .bit) := do
  let child ← Authoring.CircuitDescription.placeIndexed "eq"
    Primitives.eqDesign fun
      | .left => left
      | .right => right
  pure (child .output)

end Silean.Primitives.Eq
