import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EnabledResetRegister.Internal.EnabledResetRegisterStructure
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.ResetRegister.ResetRegisterDerived

/-! Certification machinery for the authored enabled reset register. -/

namespace Silean.Modules.EnabledResetRegister

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signalType : SignalType)
    (resetValue : signalType.Denote) for body signalType resetValue where
  selection := Mux.certification signalType,
  storage := ResetRegister.certification signalType resetValue

module_rule_schedules derivedRuleSchedules (signalType : SignalType)
    (resetValue : signalType.Denote) for body signalType resetValue
    with childContracts signalType resetValue
    implementing cycleContract signalType resetValue where
  output | .observe => [.storage => ResetRegister.Rule.observe]
  state := [.storage => ResetRegister.Rule.observe,
    .selection => Mux.Rule.select]

section LayerCertification

variable (signalType : SignalType) (resetValue : signalType.Denote)
  (layerChildren : ChildStructures (body signalType resetValue)
    (childContracts signalType resetValue))

private def stateCorresponds
    (contractState : (cycleContract signalType resetValue).state.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body signalType resetValue) layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    contractState (structuralState .storage)

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType resetValue) layerChildren)
      (cycleContract signalType resetValue)
      (stateCorresponds signalType resetValue layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have storageMatches :=
    childSolutionMatchesContract (body := body signalType resetValue)
      layerChildren hierStep satisfies .storage contractState corresponds
  derive_empty_state_child_match selectionMatches for .selection
    in body signalType resetValue from layerChildren, hierStep, satisfies
  have boundary := satisfies.1
  have storageNextCorresponds := storageMatches.nextCorresponds
  let storageInputs := (body signalType resetValue).wiring.childInputValues
    hierStep.inputs hierStep.childOutputs .storage
  let storageNextState :=
    (childContracts signalType resetValue .storage).stateRule.apply
      storageInputs contractState
  refine ⟨storageNextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (observeRule signalType resetValue).Holds
      hierStep.inputs contractState _
    rw [observeRule_holds_iff]
    have boundaryOutput := boundary .value
    change hierStep.outputs .value =
      (hierStep.children .storage).outputs .value at boundaryOutput
    exact boundaryOutput.trans
      (ResetRegister.value_of_allowed storageMatches.allowed)
  · change storageNextState =
      (cycleContract signalType resetValue).stateRule.apply
        hierStep.inputs contractState
    have storageNextValue : storageNextState .stored =
        bif hierStep.inputs .reset then resetValue
        else (hierStep.children .selection).outputs .result := by
      exact ResetRegister.next_stored_of_allowed storageMatches.allowed
    have selected := Mux.result_of_allowed signalType selectionMatches.allowed
    change (hierStep.children .selection).outputs .result =
      bif hierStep.inputs .enable then hierStep.inputs .value
        else (hierStep.children .storage).outputs .value at selected
    have storageCurrent :=
      ResetRegister.value_of_allowed storageMatches.allowed
    change (hierStep.children .storage).outputs .value =
      contractState .stored at storageCurrent
    funext statePort
    cases statePort
    rw [storageNextValue]
    change (bif hierStep.inputs .reset then resetValue
      else (hierStep.children .selection).outputs .result) =
      bif hierStep.inputs .reset then resetValue
      else bif hierStep.inputs .enable then hierStep.inputs .value
        else contractState .stored
    rw [selected, storageCurrent]

end LayerCertification

/- The enabled-reset-register wiring implements its contract using only the
public contracts of its mux and reset-register children. -/
module_cycle_certification certification (signalType : SignalType)
    (resetValue : signalType.Denote)
    for moduleStructure signalType resetValue via body signalType resetValue
    with childContracts signalType resetValue
    implementing cycleContract signalType resetValue where
  schedules := derivedRuleSchedules signalType resetValue,
  structuralChildren := structuralChildren signalType resetValue,
  certifiedChildren := certifiedChildren signalType resetValue,
  structuresMatch := certifiedChildren_moduleStructure signalType resetValue,
  stateCorresponds := stateCorresponds signalType resetValue,
  stateCoverage := fun children structuralState =>
    (children .storage).certification.hasCorrespondingState
      (structuralState .storage),
  implements := implements signalType resetValue

end Silean.Modules.EnabledResetRegister

/-! ## Authored-description correspondence -/

namespace Silean.Modules.EnabledResetRegister.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (signalType : SignalType)
    (resetValue : signalType.Denote) :
    some (description signalType resetValue) =
      ofNaming (EnabledResetRegister.naming signalType resetValue) := by
  simp only [circuit_description, description, construction,
    ResetRegister.place]
  simp [circuit_description, enumeration]
  rfl

private theorem unique (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (description signalType resetValue).UniqueNames := by
  simp only [circuit_description, description, construction,
    ResetRegister.place]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal <;> subst child <;>
    constructor <;> exact of_decide_eq_true rfl

theorem description_corresponds (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Corresponds (description signalType resetValue)
      (EnabledResetRegister.naming signalType resetValue) :=
  ⟨same signalType resetValue, unique signalType resetValue⟩

open Authoring.CircuitDescription.Description

theorem construction_correct (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (description signalType resetValue).ImplementsCycleContract
      (cycleContract signalType resetValue) (Naming.ports signalType) := by
  have corresponds := description_corresponds signalType resetValue
  unfold EnabledResetRegister.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts signalType resetValue,
      wiring := wiring signalType resetValue })
    (children := structuralChildren signalType resetValue)
    corresponds (certification signalType resetValue)

end Silean.Modules.EnabledResetRegister.Internal
