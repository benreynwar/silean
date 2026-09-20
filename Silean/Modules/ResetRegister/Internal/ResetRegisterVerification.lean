import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.ResetRegister.Internal.ResetRegisterStructure
import Silean.Modules.Register.RegisterDerived
import Silean.Modules.Mux.MuxDerived

/-! Certification machinery for the authored reset register. -/

namespace Silean.Modules.ResetRegister

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signalType : SignalType)
    (resetValue : signalType.Denote) for body signalType resetValue where
  resetValue := Constant.certification signalType resetValue,
  selection := Mux.certification signalType,
  storage := Register.certification signalType

module_rule_schedules derivedRuleSchedules (signalType : SignalType)
    (resetValue : signalType.Denote) for body signalType resetValue
    with childContracts signalType resetValue
    implementing cycleContract signalType resetValue where
  output | .observe => [.storage => Primitives.RegisterRule.observe]
  state := [.resetValue => Primitives.ConstantRule.apply,
    .selection => Mux.Rule.select,
    .storage => Primitives.RegisterRule.observe]

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
  derive_empty_state_child_match constantMatches for .resetValue
    in body signalType resetValue from layerChildren, hierStep, satisfies
  derive_empty_state_child_match selectionMatches for .selection
    in body signalType resetValue from layerChildren, hierStep, satisfies
  have storageMatches :=
    childSolutionMatchesContract (body := body signalType resetValue)
      layerChildren hierStep satisfies .storage contractState corresponds
  have boundary := satisfies.1
  have storageNextCorresponds := storageMatches.nextCorresponds
  let storageInputs := (body signalType resetValue).wiring.childInputValues
    hierStep.inputs hierStep.childOutputs .storage
  let nextState :=
    (childContracts signalType resetValue .storage).stateRule.apply
      storageInputs contractState
  refine ⟨nextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (observeRule signalType resetValue).Holds
      hierStep.inputs contractState _
    rw [observeRule_holds_iff]
    have boundaryOutput := boundary .value
    change hierStep.outputs .value =
      (hierStep.children .storage).outputs .output at boundaryOutput
    exact boundaryOutput.trans
      (Register.output_of_allowed storageMatches.allowed)
  · change nextState = (cycleContract signalType resetValue).stateRule.apply
      hierStep.inputs contractState
    have selected := Mux.cycleContract.result signalType selectionMatches.allowed
    have constantValue :=
      Constant.output_of_allowed signalType resetValue constantMatches.allowed
    change (hierStep.children .resetValue).outputs .output =
      resetValue at constantValue
    have storageNextValue :=
      Register.next_stored_of_allowed storageMatches.allowed
    change nextState .stored = storageInputs .input at storageNextValue
    change (hierStep.children .selection).outputs .result =
      bif hierStep.inputs .reset then
        (hierStep.children .resetValue).outputs .output
        else hierStep.inputs .value at selected
    funext statePort
    cases statePort
    rw [storageNextValue]
    change (hierStep.children .selection).outputs .result =
      bif hierStep.inputs .reset then resetValue else hierStep.inputs .value
    rw [selected, constantValue]

end LayerCertification

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

end Silean.Modules.ResetRegister

namespace Silean.Modules.ResetRegister.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (signalType : SignalType)
    (resetValue : signalType.Denote) :
    some (description signalType resetValue) =
      ofNaming (ResetRegister.naming signalType resetValue) := by
  simp only [circuit_description, description, construction,
    Constant.design, Constant.designWith,
    Register.place, Register.design, Register.designWith]
  simp [circuit_description, enumeration]
  unfold moduleStructure
  unfold naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming
  unfold portList
  simp only [enumeration, List.map_cons, List.map_nil]
  rw [show ((body signalType resetValue).instancePorts.ports
      .storage).inputs.labels.values = [.input] by rfl]
  dsimp [Naming.ports, body, context, instancePorts, structuralChildren, wiring,
    sourceDescription, Constant.design, Constant.designWith,
    Register.design, Register.designWith, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [enumeration, inputMap, outputMap, ports, childId, Enumeration.ordinal]
  exact of_decide_eq_true rfl

theorem description_corresponds (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Corresponds (description signalType resetValue)
      (ResetRegister.naming signalType resetValue) :=
  ⟨same signalType resetValue⟩

open Authoring.CircuitDescription.Description

theorem construction_correct (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (description signalType resetValue).ImplementsCycleContract
      (cycleContract signalType resetValue) (Naming.ports signalType) := by
  have corresponds := description_corresponds signalType resetValue
  unfold ResetRegister.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts signalType resetValue,
      wiring := wiring signalType resetValue })
    (children := structuralChildren signalType resetValue)
    corresponds (certification signalType resetValue)

end Silean.Modules.ResetRegister.Internal
