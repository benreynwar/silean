import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Modules.EnabledRegister.Internal.EnabledRegisterStructure
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.Register.RegisterDerived

/-! Certification machinery for the authored enabled register. -/

namespace Silean.Modules.EnabledRegister

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signalType : SignalType)
    for body signalType where
  selection := Modules.Mux.certification signalType,
  storage := Modules.Register.certification signalType

module_rule_schedules derivedRuleSchedules (signalType : SignalType)
    for body signalType with childContracts signalType
    implementing cycleContract signalType where
  output
    | .observe => [.storage => Primitives.RegisterRule.observe]
  state := [.storage => Primitives.RegisterRule.observe,
    .selection => Mux.Rule.select]

section LayerCertification

variable (signalType : SignalType)
  (layerChildren : ChildStructures (body signalType) (childContracts signalType))

private def stateCorresponds
    (contractState : (cycleContract signalType).state.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body signalType) layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    contractState (structuralState .storage)

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType) layerChildren)
      (cycleContract signalType) (stateCorresponds signalType layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have storageMatches :=
    childSolutionMatchesContract (body := body signalType) layerChildren hierStep
      satisfies .storage contractState corresponds
  derive_empty_state_child_match selectionMatches for .selection
    in body signalType from layerChildren, hierStep, satisfies
  have boundary := satisfies.1
  have storageNextCorresponds := storageMatches.nextCorresponds
  let storageInputs := (body signalType).wiring.childInputValues
    hierStep.inputs hierStep.childOutputs .storage
  let storageNextState :=
    (childContracts signalType .storage).stateRule.apply
      storageInputs contractState
  refine ⟨storageNextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (observeRule signalType).Holds hierStep.inputs contractState _
    rw [observeRule_holds_iff signalType]
    have boundaryOutput := boundary .q
    change hierStep.outputs .q =
      (hierStep.children .storage).outputs .output at boundaryOutput
    exact boundaryOutput.trans
      (Register.output_of_allowed storageMatches.allowed)
  · change storageNextState =
      (cycleContract signalType).stateRule.apply hierStep.inputs contractState
    have storageNextValue :=
      Register.next_stored_of_allowed storageMatches.allowed
    change storageNextState .stored = storageInputs .input at storageNextValue
    have selected := Mux.result_of_allowed signalType selectionMatches.allowed
    change (hierStep.children .selection).outputs .result =
      bif hierStep.inputs .enable then hierStep.inputs .data
        else (hierStep.children .storage).outputs .output at selected
    have storageCurrent := Register.output_of_allowed storageMatches.allowed
    change (hierStep.children .storage).outputs .output =
      contractState .stored at storageCurrent
    funext statePort
    cases statePort
    rw [storageNextValue]
    simp only [cycleContract, stateRule, Contracts.Cycle.CycleStateRule.apply]
    change (hierStep.children .selection).outputs .result =
      bif hierStep.inputs .enable then hierStep.inputs .data
        else contractState .stored
    rw [selected, storageCurrent]

end LayerCertification

module_cycle_certification certification (signalType : SignalType)
    for moduleStructure signalType via body signalType
    with childContracts signalType implementing cycleContract signalType where
  schedules := derivedRuleSchedules signalType,
  structuralChildren := structuralChildren signalType,
  certifiedChildren := certifiedChildren signalType,
  structuresMatch := certifiedChildren_moduleStructure signalType,
  stateCorresponds := stateCorresponds signalType,
  stateCoverage := fun children structuralState =>
    (children .storage).certification.hasCorrespondingState
      (structuralState .storage),
  implements := implements signalType

end Silean.Modules.EnabledRegister

namespace Silean.Modules.EnabledRegister.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (signalType : SignalType) :
    some (description signalType) =
      ofNaming (EnabledRegister.naming signalType) := by
  simp only [circuit_description, description, construction,
    Register.place, Register.design, Register.designWith]
  simp [circuit_description, enumeration]
  unfold moduleStructure naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Naming.ports, body, context, instancePorts, structuralChildren, wiring,
    sourceDescription, Register.design, Register.designWith,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [inputMap, outputMap, ports]
  rfl

private theorem unique (signalType : SignalType) :
    (description signalType).UniqueNames := by
  simp only [circuit_description, description, construction,
    Register.place, Register.design, Register.designWith]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal
  · subst child
    constructor
    · exact Mux.Naming.portNames_nodup signalType
    · exact of_decide_eq_true rfl
  · subst child
    constructor
    · rw [show (Register.Naming.namingWith signalType
          (.positional signalType)).ports =
          Register.Naming.portsWithNaming signalType (.positional signalType) by
          simp [Register.Naming.namingWith]]
      exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl

theorem description_corresponds (signalType : SignalType) :
    Corresponds (description signalType) (EnabledRegister.naming signalType) :=
  ⟨same signalType, unique signalType⟩

open Authoring.CircuitDescription.Description

theorem construction_correct (signalType : SignalType) :
    (description signalType).ImplementsCycleContract
      (cycleContract signalType) (Naming.ports signalType) := by
  have corresponds := description_corresponds signalType
  unfold EnabledRegister.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts signalType
      wiring := wiring signalType })
    (children := structuralChildren signalType)
    corresponds (certification signalType)

end Silean.Modules.EnabledRegister.Internal
