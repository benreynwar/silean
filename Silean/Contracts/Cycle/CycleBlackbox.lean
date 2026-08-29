import Silean.Contracts.Cycle.CycleImplementation

namespace Silean.Contracts.Cycle

open Silean

/-! A behavioral blackbox lets a parent be structurally composed before the
child's hardware hierarchy exists. Its simultaneous equations are exactly the
public cycle contract. It is deliberately a distinct `ModuleStructure` leaf,
so using this assumption cannot be confused with implementing the child. -/

def ModuleCycleContract.blackboxBehavior
    (contract : ModuleCycleContract ports) : Primitive where
  ports := ports
  localState := contract.state
  outputReads := ports.inputs.labels.values
  outputValues := fun inputs state => (contract.evaluate inputs state).1
  nextStateValues := fun inputs state => (contract.evaluate inputs state).2
  outputRespectsReads := by
    intro left right state agree
    have inputsEqual : left = right := by
      funext input
      apply agree input
      exact ListIndex.get_eq (ports.inputs.labels.locate input) ▸
        List.get_mem _ _
    cases inputsEqual
    rfl

def ModuleCycleContract.blackboxStructure
    (contract : ModuleCycleContract ports) : ModuleStructure ports :=
  .blackbox contract.blackboxBehavior

def ModuleCycleContract.blackboxCertification
    (contract : ModuleCycleContract ports) :
    ModuleCycleCertification contract.blackboxStructure contract where
  stateCorresponds := fun contractState structuralState =>
    contractState = structuralState
  hasCorrespondingState := fun structuralState => ⟨structuralState, rfl⟩
  hasStructuralResult := by
    intro inputs structuralState
    refine ⟨ProposedValues.blackbox
      (contract.evaluate inputs structuralState).1
      (contract.evaluate inputs structuralState).2, ?_⟩
    exact ⟨rfl, rfl⟩
  structuralResultUnique := by
    intro inputs structuralState left right leftSatisfies rightSatisfies
    cases left with
    | mk leftOutputs leftNext =>
      cases right with
      | mk rightOutputs rightNext =>
        simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          ModuleCycleContract.blackboxStructure, Primitive.IsSolution,
          Primitive.OutputsSatisfy, Primitive.NextStateSatisfy] at leftSatisfies rightSatisfies
        cases leftSatisfies.1.trans rightSatisfies.1.symm
        cases leftSatisfies.2.trans rightSatisfies.2.symm
        rfl
  implements := by
    intro inputs contractState structuralState proposal corresponds satisfies
    subst structuralState
    cases proposal with
    | mk outputs nextState =>
      simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
        ModuleCycleContract.blackboxStructure, Primitive.IsSolution,
        Primitive.OutputsSatisfy, Primitive.NextStateSatisfy,
        ModuleCycleContract.blackboxBehavior] at satisfies
      change ∃ nextContractState,
        contract.EvaluatesTo inputs contractState outputs nextContractState ∧
          nextContractState = nextState
      rw [satisfies.1, satisfies.2]
      refine ⟨(contract.evaluate inputs contractState).2,
        contract.evaluate_evaluatesTo inputs contractState, rfl⟩

def ModuleCycleContract.blackboxCertified
    (contract : ModuleCycleContract ports) : ModuleCycleCertified ports :=
  contract.blackboxCertification.bundle

@[simp] theorem ModuleCycleContract.blackboxCertified_structure
    (contract : ModuleCycleContract ports) :
    contract.blackboxCertified.moduleStructure = contract.blackboxStructure := rfl

@[simp] theorem ModuleCycleContract.blackboxCertified_contract
    (contract : ModuleCycleContract ports) :
    contract.blackboxCertified.cycleContract = contract := rfl

end Silean.Contracts.Cycle
