import Silean.Contracts.Cycle.CycleImplementation
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

private theorem eqImplements : Contracts.Cycle.Implements (.primitive eq) eqCycleContract
    eqStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    cases proposal with
    | mk outputs nextState =>
      change eqOutputRule.Holds inputs contractState outputs
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.OutputsSatisfy] at satisfies
      rw [satisfies.1]
      exact SignalGroup.matches_project _ _
  · rfl

def eqCertified : Contracts.Cycle.ModuleCycleCertified eq.ports where
  moduleStructure := .primitive eq
  cycleContract := eqCycleContract
  certification := {
    stateCorresponds := eqStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := fun inputs state =>
    ⟨ProposedValues.primitive (eq.outputValues inputs state)
      (eq.nextStateValues inputs state), by
        simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          Primitive.IsSolution, Primitive.OutputsSatisfy,
          Primitive.NextStateSatisfy, ProposedValues.primitive]⟩,
    structuralResultUnique := Primitive.hasAtMostOneSolution eq,
    implements := eqImplements }
end Silean.Primitives
