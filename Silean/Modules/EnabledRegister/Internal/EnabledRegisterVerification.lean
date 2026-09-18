import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Modules.EnabledRegister.EnabledRegister
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.Register.RegisterTheorems

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
  letI : Subsingleton (childContracts signalType .selection).state.Values := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have selectionMatches :=
    childSolutionMatchesContract_of_subsingletonState (body := body signalType)
      layerChildren hierStep satisfies .selection SignalMap.emptyValues
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
    exact boundaryOutput.trans ((Register.outputRule_holds_iff signalType _ _ _).mp
      (storageMatches.ruleHolds Primitives.RegisterRule.observe))
  · change storageNextState =
      (cycleContract signalType).stateRule.apply hierStep.inputs contractState
    have storageNextValue : storageNextState .stored =
        storageInputs .input := by
      rfl
    have selected := (Mux.selectRule_holds_iff signalType _ _ _).mp
      (selectionMatches.ruleHolds Mux.Rule.select)
    change (hierStep.children .selection).outputs .result =
      bif hierStep.inputs .enable then hierStep.inputs .data
        else (hierStep.children .storage).outputs .output at selected
    have storageCurrent := (Register.outputRule_holds_iff signalType _ _ _).mp
      (storageMatches.ruleHolds Primitives.RegisterRule.observe)
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

namespace Silean.Modules.EnabledRegister.Description.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (signalType : SignalType) :
    some (description signalType) =
      ofNaming (EnabledRegister.naming signalType) := by
  simp only [description, construction, build, buildResult,
    Mux.placeNamed, Register.placeNamed, Register.design, Register.designWith,
    Authoring.CircuitDescription.placeNamed,
    Authoring.CircuitDescription.input, Authoring.CircuitDescription.output,
    Authoring.CircuitDescription.wire, Authoring.CircuitDescription.assign,
    Authoring.CircuitDescription.bind_apply,
    Authoring.CircuitDescription.pure_apply]
  rw [show (inferInstance : Enumeration Mux.Input).values =
    [.select, .whenFalse, .whenTrue] by rfl]
  rw [show (inferInstance : Enumeration Primitives.UnaryInput).values = [.input] by rfl]
  simp [Authoring.CircuitDescription.Internal.finalizeDraft,
    Authoring.CircuitDescription.Internal.validateWireDrivers,
    Authoring.CircuitDescription.Internal.validateWireSources,
    Authoring.CircuitDescription.Internal.finalizeConnections,
    Authoring.CircuitDescription.Internal.finalizeConnection,
    Authoring.CircuitDescription.Internal.finalizeChildren,
    Authoring.CircuitDescription.Internal.finalizeChild,
    Authoring.CircuitDescription.Internal.resolveNet,
    Authoring.CircuitDescription.Internal.findWire?,
    Authoring.CircuitDescription.Internal.replaceWire]
  unfold moduleStructure naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  rw [show (inferInstance : Enumeration Input).values = [.data, .enable] by rfl]
  rw [show (inferInstance : Enumeration Output).values = [.q] by rfl]
  rw [show (inferInstance : Enumeration Instance).values = [.selection, .storage] by rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show (inferInstance : Enumeration Mux.Input).values =
    [.select, .whenFalse, .whenTrue] by rfl]
  rw [show ((body signalType).instancePorts.ports .storage).inputs.labels.values =
    [.input] by rfl]
  dsimp [Naming.ports, body, context, instancePorts, structuralChildren, wiring,
    sourceDescription, Register.design, Register.designWith,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [Naming.portsWithNaming, inputMap, outputMap, ports]

private theorem unique (signalType : SignalType) :
    (description signalType).UniqueNames := by
  simp only [description, construction, build, buildResult,
    Mux.placeNamed, Register.placeNamed, Register.design, Register.designWith,
    Authoring.CircuitDescription.placeNamed,
    Authoring.CircuitDescription.input, Authoring.CircuitDescription.output,
    Authoring.CircuitDescription.wire, Authoring.CircuitDescription.assign,
    Authoring.CircuitDescription.bind_apply,
    Authoring.CircuitDescription.pure_apply]
  rw [show (inferInstance : Enumeration Mux.Input).values =
    [.select, .whenFalse, .whenTrue] by rfl]
  rw [show (inferInstance : Enumeration Primitives.UnaryInput).values = [.input] by rfl]
  simp [Authoring.CircuitDescription.Internal.finalizeDraft,
    Authoring.CircuitDescription.Internal.validateWireDrivers,
    Authoring.CircuitDescription.Internal.validateWireSources,
    Authoring.CircuitDescription.Internal.finalizeConnections,
    Authoring.CircuitDescription.Internal.finalizeConnection,
    Authoring.CircuitDescription.Internal.finalizeChildren,
    Authoring.CircuitDescription.Internal.finalizeChild,
    Authoring.CircuitDescription.Internal.resolveNet,
    Authoring.CircuitDescription.Internal.findWire?,
    Authoring.CircuitDescription.Internal.replaceWire]
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

theorem corresponds (signalType : SignalType) :
    Corresponds (description signalType) (EnabledRegister.naming signalType) :=
  ⟨same signalType, unique signalType⟩

end Silean.Modules.EnabledRegister.Description.Internal
