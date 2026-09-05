import Silean.Contracts.Cycle.CycleImplementation
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

private theorem orImplements : Contracts.Cycle.Implements (.primitive or) orCycleContract
    orStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    cases proposal with
    | mk outputs nextState =>
      change orOutputRule.Holds inputs contractState outputs
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.OutputsSatisfy] at satisfies
      rw [satisfies.1]
      exact SignalGroup.matches_project _ _
  · rfl

def orCertified : Contracts.Cycle.ModuleCycleCertified or.ports where
  moduleStructure := .primitive or
  cycleContract := orCycleContract
  certification := {
    stateCorresponds := orStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := fun inputs state =>
    ⟨ProposedValues.primitive (or.outputValues inputs state)
      (or.nextStateValues inputs state), by
        simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          Primitive.IsSolution, Primitive.OutputsSatisfy,
          Primitive.NextStateSatisfy, ProposedValues.primitive]⟩,
    structuralResultUnique := Primitive.hasAtMostOneSolution or,
    implements := orImplements }
end Silean.Primitives
