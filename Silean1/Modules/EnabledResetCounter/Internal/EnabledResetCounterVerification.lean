import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EnabledResetCounter.Internal.EnabledResetCounterStructure
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterDerived
import Silean.Modules.Increment.IncrementDerived

/-! Certification machinery for the authored enabled reset counter. -/

namespace Silean.Modules.EnabledResetCounter

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (width : Nat)
    (resetValue : Value width) for body width resetValue where
  increment := Increment.certification width,
  storage := EnabledResetRegister.certification (valueType width) resetValue

module_rule_schedules derivedRuleSchedules (width : Nat)
    (resetValue : Value width) for body width resetValue
    with childContracts width resetValue
    implementing cycleContract width resetValue where
  output | .observe => [.storage => EnabledResetRegister.Rule.observe]
  state := [.storage => EnabledResetRegister.Rule.observe,
    .increment => Increment.Rule.apply]

section LayerCertification

variable (width : Nat) (resetValue : Value width)
  (layerChildren : ChildStructures (body width resetValue)
    (childContracts width resetValue))

private def stateCorresponds
    (contractState : (cycleContract width resetValue).state.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body width resetValue) layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    contractState (structuralState .storage)

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body width resetValue) layerChildren)
      (cycleContract width resetValue)
      (stateCorresponds width resetValue layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have storageMatches :=
    childSolutionMatchesContract (body := body width resetValue)
      layerChildren hierStep satisfies .storage contractState corresponds
  derive_empty_state_child_match incrementMatches for .increment
    in body width resetValue from layerChildren, hierStep, satisfies
  have storageAllowed := storageMatches.allowed
  have storageNextCorresponds := storageMatches.nextCorresponds
  have boundary := satisfies.1
  let storageInputs := (body width resetValue).wiring.childInputValues
    hierStep.inputs hierStep.childOutputs .storage
  let storageNextState :=
    (childContracts width resetValue .storage).stateRule.apply
      storageInputs contractState
  refine ⟨storageNextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (outputRule width).Holds
      hierStep.inputs contractState hierStep.outputs
    rw [outputRule_holds_iff]
    have boundaryOutput := boundary .value
    change hierStep.outputs .value =
      (hierStep.children .storage).outputs .value at boundaryOutput
    exact boundaryOutput.trans
      (EnabledResetRegister.cycleContract.value (valueType width) resetValue storageAllowed)
  · change storageNextState =
      (cycleContract width resetValue).stateRule.apply
        hierStep.inputs contractState
    have storageNextValue : storageNextState .stored =
        bif hierStep.inputs .reset then resetValue
        else bif hierStep.inputs .enable then
          (hierStep.children .increment).outputs .result
          else contractState .stored := by
      exact EnabledResetRegister.next_stored_of_allowed storageAllowed
    have incremented :=
      Increment.cycleContract.result width incrementMatches.allowed
    change (hierStep.children .increment).outputs .result =
      Increment.incrementValue width
        ((hierStep.children .storage).outputs .value)
      at incremented
    have storageCurrent :
        (hierStep.children .storage).outputs .value = contractState .stored := by
      exact EnabledResetRegister.cycleContract.value
        (valueType width) resetValue storageAllowed
    funext statePort
    cases statePort
    rw [storageNextValue]
    change (bif hierStep.inputs .reset then resetValue
      else bif hierStep.inputs .enable then
        (hierStep.children .increment).outputs .result
        else contractState .stored) =
      nextValue width resetValue (hierStep.inputs .enable)
        (hierStep.inputs .reset)
        (contractState .stored)
    rw [incremented, storageCurrent]
    rfl

end LayerCertification

module_cycle_certification certification (width : Nat)
    (resetValue : Value width)
    for moduleStructure width resetValue via body width resetValue
    with childContracts width resetValue
    implementing cycleContract width resetValue where
  schedules := derivedRuleSchedules width resetValue,
  structuralChildren := structuralChildren width resetValue,
  certifiedChildren := certifiedChildren width resetValue,
  structuresMatch := certifiedChildren_moduleStructure width resetValue,
  stateCorresponds := stateCorresponds width resetValue,
  stateCoverage := fun children structuralState =>
    (children .storage).certification.hasCorrespondingState
      (structuralState .storage),
  implements := implements width resetValue

end Silean.Modules.EnabledResetCounter

namespace Silean.Modules.EnabledResetCounter.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (width : Nat) (resetValue : Value width) :
    some (description width resetValue) =
      ofNaming (EnabledResetCounter.naming width resetValue) := by
  simp only [circuit_description, description, construction,
    Increment.place, EnabledResetRegister.place]
  simp [circuit_description, enumeration]
  unfold moduleStructure naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Naming.ports, body, context, instancePorts, structuralChildren, wiring,
    sourceDescription, Increment.design, EnabledResetRegister.design,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [inputMap, outputMap, ports]
  rfl

theorem description_corresponds (width : Nat) (resetValue : Value width) :
    Corresponds (description width resetValue)
      (EnabledResetCounter.naming width resetValue) :=
  ⟨same width resetValue⟩

open Authoring.CircuitDescription.Description

theorem construction_correct (width : Nat) (resetValue : Value width) :
    (description width resetValue).ImplementsCycleContract
      (cycleContract width resetValue) (Naming.ports width) := by
  have corresponds := description_corresponds width resetValue
  unfold EnabledResetCounter.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts width resetValue,
      wiring := wiring width resetValue })
    (children := structuralChildren width resetValue)
    corresponds (certification width resetValue)

end Silean.Modules.EnabledResetCounter.Internal
