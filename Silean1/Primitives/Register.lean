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

private theorem registerImplements : Contracts.Cycle.ImplementsSolutions (.primitive register)
    registerCycleContract registerStateCorresponds := by
  intro contractState hierStep corresponds satisfies
  cases hierStep with
  | mk inputs structuralState outputs nextState =>
  change contractState = structuralState at corresponds
  change outputs = register.outputValues inputs structuralState ∧
    nextState = register.nextStateValues inputs structuralState at satisfies
  refine ⟨registerStateRule.apply inputs contractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      change registerOutputRule.Holds inputs contractState outputs
      rw [satisfies.1, corresponds.symm]
      exact SignalGroup.matches_project _ _
    · rfl
  · exact (congrArg (registerStateRule.apply inputs) corresponds).trans
      satisfies.2.symm

def registerCertified : Contracts.Cycle.ModuleCycleCertified register.ports where
  moduleStructure := .primitive register
  cycleContract := registerCycleContract
  certification := {
    structural := register.structuralCertification
    stateCorresponds := registerStateCorresponds
    hasCorrespondingState := fun state => ⟨state, rfl⟩
    implements :=
      Contracts.Cycle.implementsSolutions_iff_implements.mp registerImplements }

end Silean.Primitives
