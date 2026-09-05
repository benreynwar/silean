import Silean.Contracts.Cycle.CycleImplementation
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

private theorem notImplements : Contracts.Cycle.Implements (.primitive not) notCycleContract
    notStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    cases proposal with
    | mk outputs nextState =>
      change notOutputRule.Holds inputs contractState outputs
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.OutputsSatisfy] at satisfies
      rw [satisfies.1]
      exact SignalGroup.matches_project _ _
  · rfl

def notCertified : Contracts.Cycle.ModuleCycleCertified not.ports where
  moduleStructure := .primitive not
  cycleContract := notCycleContract
  certification := {
    stateCorresponds := notStateCorresponds
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
    hasStructuralResult := fun inputs state =>
      ⟨ProposedValues.primitive (not.outputValues inputs state)
        (not.nextStateValues inputs state), by
          simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
            Primitive.IsSolution, Primitive.OutputsSatisfy,
            Primitive.NextStateSatisfy, ProposedValues.primitive]⟩
    structuralResultUnique := Primitive.hasAtMostOneSolution not
    implements := notImplements }

end Silean.Primitives
