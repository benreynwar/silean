import Silean.Authoring.CircuitDescription
import Silean.Contracts.Cycle.CycleImplementation
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.OrPrimitive

namespace Silean.Primitives

open Silean

inductive OrRule | apply
deriving Enumeration
def orOutputRule : Contracts.Cycle.CycleOutputRule or.ports emptySignalMap where
  readsInputs := .all or.ports.inputs
  writesOutputs := .all or.ports.outputs
  target inputs _ := fun | .output => inputs .left || inputs .right
def orCycleContract : Contracts.Cycle.ModuleCycleContract or.ports where
  state := emptySignalMap
  RuleName := OrRule
  ruleNames := inferInstance
  outputRule | .apply => orOutputRule
  stateRule := Contracts.Cycle.CycleStateRule.empty or.ports
  outputCoverage := by rfl

@[simp] theorem orOutputRule_holds_iff
    (inputs : or.ports.inputs.Values)
    (state : orCycleContract.state.Values)
    (outputs : or.ports.outputs.Values) :
    orOutputRule.Holds inputs state outputs ↔
      outputs .output = (inputs .left || inputs .right) := by
  simp only [orOutputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

private def orStateCorresponds (_ : orCycleContract.state.Values)
    (_ : (ModuleStructure.primitive or).State) : Prop := True

private theorem orImplements : Contracts.Cycle.ImplementsSolutions (.primitive or) orCycleContract
    orStateCorresponds := by
  intro contractState hierStep corresponds satisfies
  cases hierStep with
  | mk inputs structuralState outputs nextState =>
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change orOutputRule.Holds inputs contractState outputs
    change outputs = or.outputValues inputs structuralState ∧
      nextState = or.nextStateValues inputs structuralState at satisfies
    rw [satisfies.1]
    exact SignalGroup.matches_project _ _
  · rfl

def orCertified : Contracts.Cycle.ModuleCycleCertified or.ports where
  moduleStructure := .primitive or
  cycleContract := orCycleContract
  certification := {
    stateCorresponds := orStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := Primitive.hasSolution or,
    structuralResultUnique := Primitive.hasAtMostOneSolution or,
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp orImplements }
end Silean.Primitives

namespace Silean.Primitives.Or

open Silean.Authoring.CircuitDescription

/-- Place a one-bit OR gate under a caller-chosen instance name. -/
def placeNamed (name : Silean.Naming.SourceName)
    (left right : Net .bit) : Builder (Net .bit) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    Primitives.orDesign fun
      | .left => left
      | .right => right
  pure (child .output)

/-- Place a one-bit OR gate in a circuit description. -/
def place (left right : Net .bit) : Builder (Net .bit) := do
  let child ← Authoring.CircuitDescription.placeIndexed "or"
    Primitives.orDesign fun
      | .left => left
      | .right => right
  pure (child .output)

end Silean.Primitives.Or
