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
    Contracts.Cycle.ImplementsSolutions (.primitive (constant value))
      (constantCycleContract value)
      (stateCorresponds value) := by
  intro contractState hierStep corresponds satisfies
  cases hierStep with
  | mk inputs structuralState outputs nextState =>
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change (constantOutputRule value).Holds inputs contractState outputs
    change outputs = (constant value).outputValues inputs structuralState ∧
      nextState = (constant value).nextStateValues inputs structuralState at satisfies
    rw [satisfies.1]
    exact SignalGroup.matches_project _ _
  · rfl

def constantCertified (value : Bool) :
    Contracts.Cycle.ModuleCycleCertified (constant value).ports where
  moduleStructure := .primitive (constant value)
  cycleContract := constantCycleContract value
  certification := {
    structural := (constant value).structuralCertification
    stateCorresponds := stateCorresponds value
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp
      (implements value) }

end Silean.Primitives
