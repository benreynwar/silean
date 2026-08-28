import Silean.ModuleCycleCertified
import Silean.PrimitivePorts

namespace Silean.Primitives

open Silean

@[reducible] def register : Primitive where
  ports := unaryPorts
  localState := registerStateMap
  outputReads := []
  outputValues := fun _ state => fun | .output => state .stored
  nextStateValues := fun inputs _ => fun | .stored => inputs .input
  outputRespectsReads := by
    intro left right state agrees
    rfl

inductive RegisterRule | observe
deriving Enumeration
def registerOutputRule : CycleOutputRule register.ports registerStateMap
    (.ofLists [] [.bit]) where
  readsInputs := .nil
  writesOutputs := register.ports.outputs.select .output
  target | (), state => (state .stored, ())
def registerStateRule : CycleStateRule register.ports registerStateMap where
  inputTypes := .cons .bit .nil
  readsInputs := register.ports.inputs.select .input
  target := fun | (input, ()), _ => fun | .stored => input
def registerCycleContract : ModuleCycleContract register.ports where
  state := registerStateMap
  RuleName := RegisterRule
  ruleNames := inferInstance
  outputRule | .observe => ⟨_, registerOutputRule⟩
  stateRule := registerStateRule
  outputCoverage := by rfl

private def registerStateCorresponds
    (contractState : registerCycleContract.state.Values)
    (structuralState : (ModuleStructure.primitive register).State) : Prop :=
  contractState = structuralState

private theorem registerImplements : Implements (.primitive register)
    registerCycleContract registerStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨registerStateRule.apply inputs contractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      cases proposal with
      | mk outputs nextState =>
        change registerOutputRule.Holds inputs contractState outputs
        simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          Primitive.IsSolution, Primitive.OutputsSatisfy] at satisfies
        rw [satisfies.1, corresponds.symm]
        simp [registerOutputRule, CycleOutputRule.Holds,
          SignalSelection.project, SignalSelection.Matches, SignalMap.select,
          register]
    · rfl
  · cases proposal with
    | mk outputs nextState =>
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.NextStateSatisfy] at satisfies
      exact (congrArg (registerStateRule.apply inputs) corresponds).trans
        satisfies.2.symm

def registerCertified : ModuleCycleCertified register.ports where
  moduleStructure := .primitive register
  cycleContract := registerCycleContract
  certification := {
    stateCorresponds := registerStateCorresponds,
    hasCorrespondingState := fun state => ⟨state, rfl⟩,
    hasStructuralResult := fun inputs state =>
    ⟨ProposedValues.primitive (register.outputValues inputs state)
      (register.nextStateValues inputs state), by
        simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          Primitive.IsSolution, Primitive.OutputsSatisfy,
          Primitive.NextStateSatisfy, ProposedValues.primitive]⟩,
    structuralResultUnique := Primitive.hasAtMostOneSolution register,
    implements := registerImplements }
end Silean.Primitives
