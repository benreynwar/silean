import Silean.Contracts.Cycle.CycleImplementation
import Silean.Naming.ModuleNaming

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

/-- Give a cycle contract's structural blackbox the executable naming needed
to use it as a child of `module_design`. The state names are internal emission
metadata; the contract boundary keeps the supplied port naming. -/
@[reducible] def ModuleCycleContract.blackboxDesign
    (contract : ModuleCycleContract ports) (name : String)
    (portsNaming : Naming.ModulePortsNaming ports) : Naming.NamedModule :=
  ⟨ports, contract.blackboxStructure,
    .blackbox ⟨name, "", []⟩ portsNaming
      (Naming.SignalMapNaming.indexed contract.state "state")⟩

def ModuleCycleContract.blackboxCertification
    (contract : ModuleCycleContract ports) :
    ModuleCycleCertification contract.blackboxStructure contract where
  structural := {
    hasSolution := by
      intro inputs structuralState
      let hierStep : HierStep contract.blackboxStructure :=
        { inputs := inputs
          currentState := structuralState
          outputs := (contract.evaluate inputs structuralState).1
          nextState := (contract.evaluate inputs structuralState).2 }
      refine ⟨hierStep, ?_, rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    hasAtMostOneSolution :=
      Primitive.blackbox_hasAtMostOneSolution contract.blackboxBehavior }
  stateCorresponds := fun contractState structuralState =>
    contractState = structuralState
  hasCorrespondingState := fun structuralState => ⟨structuralState, rfl⟩
  implements := implementsSolutions_iff_implements.mp (by
    intro contractState hierStep corresponds satisfies
    cases hierStep with
    | mk inputs structuralState outputs nextState =>
      change contractState = structuralState at corresponds
      subst structuralState
      change outputs = (contract.evaluate inputs contractState).1 ∧
        nextState = (contract.evaluate inputs contractState).2 at satisfies
      rw [satisfies.1, satisfies.2]
      exact ⟨(contract.evaluate inputs contractState).2,
        contract.evaluateStep_allowed inputs contractState, rfl⟩)

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
