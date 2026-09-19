import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EnabledResetCounter.EnabledResetCounter
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterTheorems
import Silean.Modules.Increment.IncrementTheorems

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
  letI : Subsingleton (childContracts width resetValue .increment).state.Values := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have incrementMatches :=
    childSolutionMatchesContract_of_subsingletonState
      (body := body width resetValue) layerChildren hierStep satisfies
      .increment SignalMap.emptyValues
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
      (EnabledResetRegister.value_of_allowed storageAllowed)
  · change storageNextState =
      (cycleContract width resetValue).stateRule.apply
        hierStep.inputs contractState
    have storageNextValue : storageNextState .stored =
        bif hierStep.inputs .reset then resetValue
        else bif hierStep.inputs .enable then
          (hierStep.children .increment).outputs .result
          else contractState .stored := by
      exact EnabledResetRegister.next_stored_of_allowed storageAllowed
    have incremented := (Increment.outputRule_holds_iff width _ _ _).mp
      (incrementMatches.ruleHolds Increment.Rule.apply)
    change (hierStep.children .increment).outputs .result =
      Increment.incrementValue width
        ((hierStep.children .storage).outputs .value)
      at incremented
    have storageCurrent :
        (hierStep.children .storage).outputs .value = contractState .stored := by
      exact EnabledResetRegister.value_of_allowed storageAllowed
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

namespace Silean.Modules.EnabledResetCounter.Description.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (width : Nat) (resetValue : Value width) :
    some (description width resetValue) =
      ofNaming (EnabledResetCounter.naming width resetValue) := by
  simp only [circuit_description, description, construction,
    Increment.place, EnabledResetRegister.place,
    EnabledResetRegister.design]
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

private theorem unique (width : Nat) (resetValue : Value width) :
    (description width resetValue).UniqueNames := by
  simp only [circuit_description, description, construction,
    Increment.place, EnabledResetRegister.place,
    EnabledResetRegister.design]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal
  · subst child
    exact ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩
  · subst child
    constructor
    · change (EnabledResetRegister.Naming.portsWithNaming
          (valueType width) (.positional (valueType width))).names.Nodup
      exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl

theorem corresponds (width : Nat) (resetValue : Value width) :
    Corresponds (description width resetValue)
      (EnabledResetCounter.naming width resetValue) :=
  ⟨same width resetValue, unique width resetValue⟩

end Silean.Modules.EnabledResetCounter.Description.Internal
