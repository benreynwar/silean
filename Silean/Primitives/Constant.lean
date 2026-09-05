import Silean.Contracts.Cycle.CycleImplementation
import Silean.Primitives.ConstantPrimitive

namespace Silean.Primitives

open Silean

inductive ConstantRule | apply
deriving Enumeration

def constantOutputRule (value : Bool) :
    Contracts.Cycle.CycleOutputRule (constant value).ports emptySignalMap where
  readsInputs := .empty (constant value).ports.inputs
  writesOutputs := .all (constant value).ports.outputs
  target _ _ := fun | .output => value

def constantCycleContract (value : Bool) :
    Contracts.Cycle.ModuleCycleContract (constant value).ports where
  state := emptySignalMap
  RuleName := ConstantRule
  ruleNames := inferInstance
  outputRule | .apply => constantOutputRule value
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem constantOutputRule_holds_iff (value : Bool)
    (inputs : (constant value).ports.inputs.Values)
    (state : (constantCycleContract value).state.Values)
    (outputs : (constant value).ports.outputs.Values) :
    (constantOutputRule value).Holds inputs state outputs ↔ outputs .output = value := by
  simp only [constantOutputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

private def stateCorresponds (value : Bool)
    (_ : (constantCycleContract value).state.Values)
    (_ : (ModuleStructure.primitive (constant value)).State) : Prop := True

private theorem implements (value : Bool) :
    Contracts.Cycle.Implements (.primitive (constant value)) (constantCycleContract value)
      (stateCorresponds value) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    cases proposal with
    | mk outputs nextState =>
      change (constantOutputRule value).Holds inputs contractState outputs
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.OutputsSatisfy] at satisfies
      rw [satisfies.1]
      exact SignalGroup.matches_project _ _
  · rfl

def constantCertified (value : Bool) :
    Contracts.Cycle.ModuleCycleCertified (constant value).ports where
  moduleStructure := .primitive (constant value)
  cycleContract := constantCycleContract value
  certification := {
    stateCorresponds := stateCorresponds value
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
    hasStructuralResult := fun inputs state =>
      ⟨ProposedValues.primitive ((constant value).outputValues inputs state)
        ((constant value).nextStateValues inputs state), by
          simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
            Primitive.IsSolution, Primitive.OutputsSatisfy,
            Primitive.NextStateSatisfy, ProposedValues.primitive]⟩
    structuralResultUnique := Primitive.hasAtMostOneSolution (constant value)
    implements := implements value }

end Silean.Primitives
