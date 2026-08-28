import Silean.ModuleCycleCertified
import Silean.PrimitivePorts

namespace Silean.Primitives

open Silean

@[reducible] def constant (value : Bool) : Primitive where
  ports := constantPorts
  localState := emptySignalMap
  outputReads := []
  outputValues := fun _ _ => fun | .output => value
  nextStateValues := fun _ state => state
  outputRespectsReads := by
    intro left right state agrees
    rfl

inductive ConstantRule | apply
deriving Enumeration

def constantOutputRule (value : Bool) :
    CycleOutputRule (constant value).ports emptySignalMap
      (.ofLists [] [.bit]) where
  readsInputs := .nil
  writesOutputs := (constant value).ports.outputs.select .output
  target | (), _ => (value, ())

def constantCycleContract (value : Bool) :
    ModuleCycleContract (constant value).ports where
  state := emptySignalMap
  RuleName := ConstantRule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, constantOutputRule value⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem constantOutputRule_holds_iff (value : Bool)
    (inputs : (constant value).ports.inputs.Values)
    (state : (constantCycleContract value).state.Values)
    (outputs : (constant value).ports.outputs.Values) :
    (constantOutputRule value).Holds inputs state outputs ↔
      outputs .output = value := by
  simp [constantOutputRule, CycleOutputRule.Holds, SignalSelection.project,
    SignalSelection.Matches, SignalMap.select]

private def stateCorresponds (value : Bool)
    (_ : (constantCycleContract value).state.Values)
    (_ : (ModuleStructure.primitive (constant value)).State) : Prop := True

private theorem implements (value : Bool) :
    Implements (.primitive (constant value)) (constantCycleContract value)
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
      simp [constantOutputRule, CycleOutputRule.Holds,
        SignalSelection.project, SignalSelection.Matches, SignalMap.select,
        constant]
  · rfl

def constantCertified (value : Bool) :
    ModuleCycleCertified (constant value).ports where
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
