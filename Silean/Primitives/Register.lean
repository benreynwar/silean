import Silean.Contracts.Cycle.CycleImplementation
import Silean.Primitives.RegisterPrimitive

namespace Silean.Primitives

open Silean

inductive RegisterRule | observe
deriving Enumeration

def registerOutputRule : Contracts.Cycle.CycleOutputRule register.ports registerStateMap where
  readsInputs := .empty register.ports.inputs
  writesOutputs := .all register.ports.outputs
  target _ state := fun | .output => state .stored

def registerStateRule : Contracts.Cycle.CycleStateRule register.ports registerStateMap where
  readsInputs := .all register.ports.inputs
  target := fun inputs _ => fun | .stored => inputs .input

def registerCycleContract : Contracts.Cycle.ModuleCycleContract register.ports where
  state := registerStateMap
  RuleName := RegisterRule
  ruleNames := inferInstance
  outputRule | .observe => registerOutputRule
  stateRule := registerStateRule
  outputCoverage := by rfl

private def registerStateCorresponds
    (contractState : registerCycleContract.state.Values)
    (structuralState : (ModuleStructure.primitive register).State) : Prop :=
  contractState = structuralState

private theorem registerImplements : Contracts.Cycle.Implements (.primitive register)
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
        exact SignalGroup.matches_project _ _
    · rfl
  · cases proposal with
    | mk outputs nextState =>
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        Primitive.IsSolution, Primitive.NextStateSatisfy] at satisfies
      exact (congrArg (registerStateRule.apply inputs) corresponds).trans satisfies.2.symm

def registerCertified : Contracts.Cycle.ModuleCycleCertified register.ports where
  moduleStructure := .primitive register
  cycleContract := registerCycleContract
  certification := {
    stateCorresponds := registerStateCorresponds
    hasCorrespondingState := fun state => ⟨state, rfl⟩
    hasStructuralResult := fun inputs state =>
      ⟨ProposedValues.primitive (register.outputValues inputs state)
        (register.nextStateValues inputs state), by
          simp [ModuleStructure.IsSolution, ProposedValues.IsSolution,
            Primitive.IsSolution, Primitive.OutputsSatisfy,
            Primitive.NextStateSatisfy, ProposedValues.primitive]⟩
    structuralResultUnique := Primitive.hasAtMostOneSolution register
    implements := registerImplements }

end Silean.Primitives
