import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.ResetRegister.ResetRegister
import Silean.Modules.Register.RegisterTheorems
import Silean.Modules.Mux.MuxTheorems

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
  have statelessChildState (child : Instance)
      (h : child = .resetValue ∨ child = .selection) :
      Subsingleton (childContracts signalType resetValue child).state.Values := by
    rcases h with rfl | rfl <;>
      change Subsingleton emptySignalMap.Values <;> infer_instance
  have constantMatches :=
    letI := statelessChildState .resetValue (Or.inl rfl)
    childSolutionMatchesContract_of_subsingletonState
      (body := body signalType resetValue) layerChildren hierStep satisfies
      .resetValue SignalMap.emptyValues
  have selectionMatches :=
    letI := statelessChildState .selection (Or.inr rfl)
    childSolutionMatchesContract_of_subsingletonState
      (body := body signalType resetValue) layerChildren hierStep satisfies
      .selection SignalMap.emptyValues
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
      ((Register.outputRule_holds_iff signalType _ _ _).mp
        (storageMatches.ruleHolds Primitives.RegisterRule.observe))
  · change nextState = (cycleContract signalType resetValue).stateRule.apply
      hierStep.inputs contractState
    have selected := (Mux.selectRule_holds_iff signalType _ _ _).mp
      (selectionMatches.ruleHolds Mux.Rule.select)
    have constantValue := (Constant.outputRule_holds_iff signalType resetValue _ _ _).mp
      (constantMatches.ruleHolds Primitives.ConstantRule.apply)
    change (hierStep.children .resetValue).outputs .output =
      resetValue at constantValue
    have storageNextValue : nextState .stored =
        storageInputs .input := by
      rfl
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

namespace Silean.Modules.ResetRegister.Description.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (signalType : SignalType)
    (resetValue : signalType.Denote) :
    some (description signalType resetValue) =
      ofNaming (ResetRegister.naming signalType resetValue) := by
  simp only [description, construction, build, buildResult,
    Constant.placeNamed, Constant.design, Constant.designWith,
    Mux.placeNamed, Register.placeNamed, Register.design, Register.designWith,
    Naming.ModuleNaming.ports_withPorts,
    Authoring.CircuitDescription.placeNamed,
    Authoring.CircuitDescription.input, Authoring.CircuitDescription.output,
    Authoring.CircuitDescription.bind_apply,
    Authoring.CircuitDescription.pure_apply]
  rw [show (inferInstance : Enumeration Mux.Input).values =
    [.select, .whenFalse, .whenTrue] by rfl]
  rw [show (inferInstance : Enumeration NoSignal).values = [] by rfl]
  rw [show (inferInstance : Enumeration Primitives.UnaryInput).values = [.input] by rfl]
  simp [Authoring.CircuitDescription.Internal.finalizeDraft,
    Authoring.CircuitDescription.Internal.validateWireDrivers,
    Authoring.CircuitDescription.Internal.validateWireSources,
    Authoring.CircuitDescription.Internal.finalizeConnections,
    Authoring.CircuitDescription.Internal.finalizeConnection,
    Authoring.CircuitDescription.Internal.finalizeChildren,
    Authoring.CircuitDescription.Internal.finalizeChild,
    Authoring.CircuitDescription.Internal.resolveNet]
  unfold moduleStructure
  unfold naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming
  unfold portList
  rw [show (inferInstance : Enumeration Input).values = [.value, .reset] by rfl]
  rw [show (inferInstance : Enumeration Output).values = [.value] by rfl]
  rw [show (inferInstance : Enumeration Instance).values =
    [.resetValue, .selection, .storage] by rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show (inferInstance : Enumeration NoSignal).values = [] by rfl]
  rw [show (inferInstance : Enumeration Mux.Input).values =
    [.select, .whenFalse, .whenTrue] by rfl]
  rw [show ((body signalType resetValue).instancePorts.ports
      .storage).inputs.labels.values = [.input] by rfl]
  dsimp [Naming.ports, body, context, instancePorts, structuralChildren, wiring,
    sourceDescription, Constant.design, Constant.designWith,
    Register.design, Register.designWith, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [Naming.portsWithNaming, inputMap, outputMap, ports]

private theorem unique (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (description signalType resetValue).UniqueNames := by
  simp only [description, construction, build, buildResult,
    Constant.placeNamed, Constant.design, Constant.designWith,
    Mux.placeNamed, Register.placeNamed, Register.design, Register.designWith,
    Naming.ModuleNaming.ports_withPorts,
    Authoring.CircuitDescription.placeNamed,
    Authoring.CircuitDescription.input, Authoring.CircuitDescription.output,
    Authoring.CircuitDescription.bind_apply,
    Authoring.CircuitDescription.pure_apply]
  rw [show (inferInstance : Enumeration Mux.Input).values =
    [.select, .whenFalse, .whenTrue] by rfl]
  rw [show (inferInstance : Enumeration NoSignal).values = [] by rfl]
  rw [show (inferInstance : Enumeration Primitives.UnaryInput).values = [.input] by rfl]
  simp [Authoring.CircuitDescription.Internal.finalizeDraft,
    Authoring.CircuitDescription.Internal.validateWireDrivers,
    Authoring.CircuitDescription.Internal.validateWireSources,
    Authoring.CircuitDescription.Internal.finalizeConnections,
    Authoring.CircuitDescription.Internal.finalizeConnection,
    Authoring.CircuitDescription.Internal.finalizeChildren,
    Authoring.CircuitDescription.Internal.finalizeChild,
    Authoring.CircuitDescription.Internal.resolveNet]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal
  · subst child
    constructor
    · rw [Naming.ModuleNaming.ports_withPorts]
      change (Constant.Naming.portsWithNaming signalType
          (.positional signalType)).names.Nodup
      exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
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

theorem corresponds (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Corresponds (description signalType resetValue)
      (ResetRegister.naming signalType resetValue) :=
  ⟨same signalType resetValue, unique signalType resetValue⟩

end Silean.Modules.ResetRegister.Description.Internal
