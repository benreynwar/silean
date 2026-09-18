import Silean.Contracts.Cycle.CycleImplementation
import Silean.Authoring.CircuitDescription
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.AndPrimitive

namespace Silean.Primitives

open Silean

inductive AndRule | apply
deriving Enumeration
def andOutputRule : Contracts.Cycle.CycleOutputRule and.ports emptySignalMap where
  readsInputs := .all and.ports.inputs
  writesOutputs := .all and.ports.outputs
  target inputs _ := fun | .output => inputs .left && inputs .right
def andCycleContract : Contracts.Cycle.ModuleCycleContract and.ports where
  state := emptySignalMap
  RuleName := AndRule
  ruleNames := inferInstance
  outputRule | .apply => andOutputRule
  stateRule := Contracts.Cycle.CycleStateRule.empty and.ports
  outputCoverage := by rfl

@[simp] theorem andOutputRule_holds_iff
    (inputs : and.ports.inputs.Values)
    (state : andCycleContract.state.Values)
    (outputs : and.ports.outputs.Values) :
    andOutputRule.Holds inputs state outputs ↔
      outputs .output = (inputs .left && inputs .right) := by
  simp only [andOutputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

private def andStateCorresponds (_ : andCycleContract.state.Values)
    (_ : (ModuleStructure.primitive and).State) : Prop := True

private theorem andImplements : Contracts.Cycle.ImplementsSolutions (.primitive and) andCycleContract
    andStateCorresponds := by
  intro contractState hierStep corresponds satisfies
  cases hierStep with
  | mk inputs structuralState outputs nextState =>
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change andOutputRule.Holds inputs contractState outputs
    change outputs = and.outputValues inputs structuralState ∧
      nextState = and.nextStateValues inputs structuralState at satisfies
    rw [satisfies.1]
    exact SignalGroup.matches_project _ _
  · rfl

def andCertified : Contracts.Cycle.ModuleCycleCertified and.ports where
  moduleStructure := .primitive and
  cycleContract := andCycleContract
  certification := {
    stateCorresponds := andStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := Primitive.hasSolution and,
    structuralResultUnique := Primitive.hasAtMostOneSolution and,
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp andImplements }
end Silean.Primitives

namespace Silean.Primitives.And

open Silean.Authoring.CircuitDescription

/-- Place a one-bit AND gate in a circuit description. -/
def place (left right : Net .bit) : Builder (Net .bit) := do
  let child ← Authoring.CircuitDescription.placeIndexed "and"
    Primitives.andDesign fun
      | .left => left
      | .right => right
  pure (child .output)

end Silean.Primitives.And
