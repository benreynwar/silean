import Silean.Contracts.Cycle.CycleImplementation
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

private theorem andImplements : Contracts.Cycle.Implements (.primitive and) andCycleContract
    andStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    cases proposal with
    | mk outputs nextState =>
      change andOutputRule.Holds inputs contractState outputs
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.OutputsSatisfy] at satisfies
      rw [satisfies.1]
      exact SignalGroup.matches_project _ _
  · rfl

def andCertified : Contracts.Cycle.ModuleCycleCertified and.ports where
  moduleStructure := .primitive and
  cycleContract := andCycleContract
  certification := {
    stateCorresponds := andStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := fun inputs state =>
    ⟨ProposedValues.primitive (and.outputValues inputs state)
      (and.nextStateValues inputs state), by
        simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          Primitive.IsSolution, Primitive.OutputsSatisfy,
          Primitive.NextStateSatisfy, ProposedValues.primitive]⟩,
    structuralResultUnique := Primitive.hasAtMostOneSolution and,
    implements := andImplements }
end Silean.Primitives
