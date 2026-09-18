import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EnabledRegister.EnabledRegisterTheorems
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterTheorems
import Silean.Modules.OneEntryFifo.Control.OneEntryFifoControlTheorems
import Silean.Modules.OneEntryFifo.OneEntryFifo
import Silean.Modules.Mux.MuxTheorems
import Silean.Primitives.Or

namespace Silean.Modules.OneEntryFifo

open Silean
open Contracts.Fifo.Cycle
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signalType : SignalType)
    for body signalType where
  validStorage := EnabledResetRegister.certification .bit false,
  dataStorage := EnabledRegister.certification signalType,
  control := OneEntryFifo.Control.certification,
  outputValidOr := Primitives.orCertified.certification,
  outputDataMux := Mux.certification signalType

module_rule_schedules derivedRuleSchedules (signalType : SignalType)
    for body signalType with childContracts signalType
    implementing cycleContract signalType where
  output
    | .forward => [.validStorage => EnabledResetRegister.Rule.observe,
      .dataStorage => EnabledRegister.Rule.observe,
      .outputValidOr => Primitives.OrRule.apply,
      .outputDataMux => Mux.Rule.select]
    | .ready => [.validStorage => EnabledResetRegister.Rule.observe,
      .control => OneEntryFifo.Control.Rule.control]
  state := [.validStorage => EnabledResetRegister.Rule.observe,
    .dataStorage => EnabledRegister.Rule.observe,
    .control => OneEntryFifo.Control.Rule.control,
    .outputValidOr => Primitives.OrRule.apply,
    .outputDataMux => Mux.Rule.select]

section LayerCertification

variable (signalType : SignalType)
  (layerChildren : ChildStructures
    (body signalType) (childContracts signalType))

private def stateCorresponds
    (contractState : (cycleContract signalType).state.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body signalType) layerChildren).State) : Prop :=
  (layerChildren .validStorage).certification.stateCorresponds
      (fun | .stored => contractState .storedValid)
      (structuralState .validStorage) ∧
    (layerChildren .dataStorage).certification.stateCorresponds
      (fun | .stored => contractState .storedData)
      (structuralState .dataStorage)

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType) layerChildren)
      (cycleContract signalType)
      (stateCorresponds signalType layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let validState : (EnabledResetRegister.cycleContract .bit false).state.Values :=
    fun | .stored => contractState .storedValid
  let dataState : (EnabledRegister.cycleContract signalType).state.Values :=
    fun | .stored => contractState .storedData
  have validCorresponds :
      (layerChildren .validStorage).certification.stateCorresponds
      validState
      (HierStep.currentState (layerChildren .validStorage).moduleStructure
        (hierStep.children .validStorage)) := corresponds.1
  have dataCorresponds :
      (layerChildren .dataStorage).certification.stateCorresponds
      dataState
      (HierStep.currentState (layerChildren .dataStorage).moduleStructure
        (hierStep.children .dataStorage)) := corresponds.2
  have validMatches := childSolutionMatchesContract
    (body := body signalType) layerChildren hierStep satisfies
    .validStorage validState validCorresponds
  have dataMatches := childSolutionMatchesContract
    (body := body signalType) layerChildren hierStep satisfies
    .dataStorage dataState dataCorresponds
  have controlMatches :=
    letI : Subsingleton (childContracts signalType .control).state.Values := by
      change Subsingleton emptySignalMap.Values; infer_instance
    childSolutionMatchesContract_of_subsingletonState
      (body := body signalType) layerChildren hierStep satisfies
      .control SignalMap.emptyValues
  have validOrMatches :=
    letI : Subsingleton (childContracts signalType .outputValidOr).state.Values := by
      change Subsingleton emptySignalMap.Values; infer_instance
    childSolutionMatchesContract_of_subsingletonState
      (body := body signalType) layerChildren hierStep satisfies
      .outputValidOr SignalMap.emptyValues
  have muxMatches :=
    letI : Subsingleton (childContracts signalType .outputDataMux).state.Values := by
      change Subsingleton emptySignalMap.Values; infer_instance
    childSolutionMatchesContract_of_subsingletonState
      (body := body signalType) layerChildren hierStep satisfies
      .outputDataMux SignalMap.emptyValues
  have boundary := satisfies.1
  let validInputs := (body signalType).wiring.childInputValues
    hierStep.inputs hierStep.childOutputs Instance.validStorage
  let dataInputs := (body signalType).wiring.childInputValues
    hierStep.inputs hierStep.childOutputs Instance.dataStorage
  have validAllowed := validMatches.allowed
  have validNextCorresponds := validMatches.nextCorresponds
  have dataAllowed := dataMatches.allowed
  have dataNextCorresponds := dataMatches.nextCorresponds
  have controlAllowed := controlMatches.allowed
  have muxAllowed := muxMatches.allowed
  let validNext := (EnabledResetRegister.cycleContract .bit false).stateRule.apply
    validInputs validState
  let dataNext := (EnabledRegister.cycleContract signalType).stateRule.apply
    dataInputs dataState
  refine ⟨(cycleContract signalType).stateRule.apply hierStep.inputs contractState, ?_, ?_⟩
  · constructor
    · intro name
      cases name
      · change (forwardRule signalType).Holds hierStep.inputs contractState _
        rw [forwardRule_holds_iff signalType]
        have validEquation := EnabledResetRegister.value_of_allowed validAllowed
        have dataEquation := EnabledRegister.q_of_allowed dataAllowed
        have muxRule := Mux.result_of_allowed signalType muxAllowed
        normalize_child_hyp validEquation
        normalize_child_hyp dataEquation
        normalize_child_hyp muxRule unfolding wiring, context
        change (hierStep.children .validStorage).outputs .value =
          contractState .storedValid at validEquation
        change (hierStep.children .dataStorage).outputs .q =
          contractState .storedData at dataEquation
        have outputOr := (Primitives.orOutputRule_holds_iff _ _ _).mp
          (validOrMatches.ruleHolds Primitives.OrRule.apply)
        normalize_child_hyp outputOr unfolding wiring, context
        have validBoundary := boundary Interfaces.Fifo.Output.outputValid
        change hierStep.outputs .outputValid =
          (hierStep.children .outputValidOr).outputs .output at validBoundary
        have dataBoundary := boundary Interfaces.Fifo.Output.outputData
        change hierStep.outputs .outputData =
          (hierStep.children .outputDataMux).outputs .result at dataBoundary
        constructor
        · exact validBoundary.trans (outputOr.trans
            (congrArg (fun value => value || hierStep.inputs .inputValid) validEquation))
        · have pairEqual :
              ((hierStep.children .validStorage).outputs .value,
                (hierStep.children .dataStorage).outputs .q) =
              (contractState .storedValid, contractState .storedData) :=
            Prod.ext validEquation dataEquation
          exact dataBoundary.trans (muxRule.trans (congrArg
            (fun pair => bif pair.1 then pair.2
              else hierStep.inputs .inputData) pairEqual))
      · change (readyRule signalType).Holds hierStep.inputs contractState _
        rw [readyRule_holds_iff signalType]
        have controlReady := OneEntryFifo.Control.upstreamReady_of_allowed
          controlAllowed
        have validEquation := EnabledResetRegister.value_of_allowed validAllowed
        normalize_child_hyp controlReady unfolding wiring, context
        normalize_child_hyp validEquation
        change (hierStep.children .validStorage).outputs .value =
          contractState .storedValid at validEquation
        have readyBoundary := boundary Interfaces.Fifo.Output.inputReady
        change hierStep.outputs .inputReady =
          (hierStep.children .control).outputs .upstreamReady at readyBoundary
        exact readyBoundary.trans (controlReady.trans (congrArg
          (fun value => hierStep.inputs .outputReady || !value) validEquation))
    · rfl
  · have controlUpdate := OneEntryFifo.Control.storageUpdate_of_allowed
      controlAllowed
    have validOutputRule := EnabledResetRegister.value_of_allowed validAllowed
    normalize_child_hyp controlUpdate unfolding wiring, context
    normalize_child_hyp validOutputRule
    change (hierStep.children .validStorage).outputs .value =
      contractState .storedValid at validOutputRule
    have updateEquation := controlUpdate
    change (hierStep.children .control).outputs .storageUpdate =
      ((hierStep.inputs .outputReady && (hierStep.children .validStorage).outputs .value) ||
        (!hierStep.inputs .outputReady && !(hierStep.children .validStorage).outputs .value)) at updateEquation
    rw [validOutputRule] at updateEquation
    have validNextEquation : validNext .stored =
        bif validInputs .reset then false
        else bif validInputs .enable then validInputs .value else validState .stored := by
      exact EnabledResetRegister.next_stored_of_allowed validAllowed
    have dataNextEquation : dataNext .stored =
        bif dataInputs .enable then dataInputs .data else dataState .stored := by
      exact EnabledRegister.next_stored_of_allowed dataAllowed
    let nextValidState : (EnabledResetRegister.cycleContract .bit false).state.Values :=
      fun | .stored => (cycleContract signalType).stateRule.apply hierStep.inputs contractState .storedValid
    let nextDataState : (EnabledRegister.cycleContract signalType).state.Values :=
      fun | .stored => (cycleContract signalType).stateRule.apply hierStep.inputs contractState .storedData
    have validNextEq : nextValidState = validNext := by
      funext statePort
      cases statePort
      rw [validNextEquation]
      change (bif hierStep.inputs .reset then false else
          bif ((hierStep.inputs .outputReady && contractState .storedValid) ||
            (!hierStep.inputs .outputReady && !contractState .storedValid)) then
            hierStep.inputs .inputValid else contractState .storedValid) =
        bif hierStep.inputs .reset then false else
          bif (hierStep.children .control).outputs .storageUpdate then
            hierStep.inputs .inputValid else contractState .storedValid
      rw [updateEquation]
    have dataNextEq : nextDataState = dataNext := by
      funext statePort
      cases statePort
      rw [dataNextEquation]
      change (bif ((hierStep.inputs .outputReady && contractState .storedValid) ||
          (!hierStep.inputs .outputReady && !contractState .storedValid)) then
          hierStep.inputs .inputData else contractState .storedData) =
        bif (hierStep.children .control).outputs .storageUpdate then
          hierStep.inputs .inputData else contractState .storedData
      rw [updateEquation]
    change (layerChildren .validStorage).certification.stateCorresponds
        nextValidState
        (HierStep.nextState (layerChildren .validStorage).moduleStructure
          (hierStep.children .validStorage)) ∧
      (layerChildren .dataStorage).certification.stateCorresponds
        nextDataState
        (HierStep.nextState (layerChildren .dataStorage).moduleStructure
          (hierStep.children .dataStorage))
    constructor
    · rw [validNextEq]
      exact validNextCorresponds
    · rw [dataNextEq]
      exact dataNextCorresponds

private theorem hasCorrespondingState
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body signalType) layerChildren).State) :
    ∃ contractState,
      stateCorresponds signalType layerChildren contractState structuralState := by
  rcases (layerChildren .validStorage).certification.hasCorrespondingState
      (structuralState .validStorage) with ⟨validState, validCorresponds⟩
  rcases (layerChildren .dataStorage).certification.hasCorrespondingState
      (structuralState .dataStorage) with ⟨dataState, dataCorresponds⟩
  exact ⟨(fun
    | .storedValid => validState .stored
    | .storedData => dataState .stored), ⟨validCorresponds, dataCorresponds⟩⟩

end LayerCertification

/- The one-entry FIFO wiring implements its contract using only the five
declared child boundary contracts. -/
module_cycle_certification certification (signalType : SignalType)
    for moduleStructure signalType via body signalType
    with childContracts signalType implementing cycleContract signalType where
  schedules := derivedRuleSchedules signalType,
  structuralChildren := structuralChildren signalType,
  certifiedChildren := certifiedChildren signalType,
  structuresMatch := certifiedChildren_moduleStructure signalType,
  stateCorresponds := stateCorresponds signalType,
  stateCoverage := hasCorrespondingState signalType,
  implements := implements signalType

end Silean.Modules.OneEntryFifo

/-! ## Authored-description correspondence -/

namespace Silean.Modules.OneEntryFifo.Description.Internal

open Silean Naming Authoring.CircuitDescription

set_option maxHeartbeats 1000000 in
private theorem same (signalType : SignalType) :
    some (description signalType) =
      ofNaming (OneEntryFifo.naming signalType) := by
  simp only [description, construction, build, buildResult,
    EnabledResetRegister.placeNamed, EnabledRegister.placeNamed,
    OneEntryFifo.Control.placeNamed, Primitives.Or.placeNamed, Mux.placeNamed,
    EnabledResetRegister.design, EnabledRegister.design,
    Authoring.CircuitDescription.placeNamed,
    Authoring.CircuitDescription.input, Authoring.CircuitDescription.output,
    Authoring.CircuitDescription.wire, Authoring.CircuitDescription.assign,
    Authoring.CircuitDescription.bind_apply,
    Authoring.CircuitDescription.pure_apply]
  simp only [show (inferInstance : Enumeration EnabledResetRegister.Input).values =
      [.value, .enable, .reset] by rfl,
    show (inferInstance : Enumeration EnabledRegister.Input).values =
      [.data, .enable] by rfl,
    show (inferInstance : Enumeration Control.Input).values =
      [.storedValid, .downstreamReady] by rfl,
    show (inferInstance : Enumeration Primitives.BinaryInput).values =
      [.left, .right] by rfl,
    show (inferInstance : Enumeration Mux.Input).values =
      [.select, .whenFalse, .whenTrue] by rfl]
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
  rw [show (inferInstance : Enumeration Interfaces.Fifo.Input).values =
    [.inputValid, .inputData, .outputReady, .reset] by rfl]
  rw [show (inferInstance : Enumeration Interfaces.Fifo.Output).values =
    [.outputValid, .outputData, .inputReady] by rfl]
  rw [show (inferInstance : Enumeration Instance).values =
    [.validStorage, .dataStorage, .control, .outputValidOr, .outputDataMux] by rfl]
  simp only [List.map_cons, List.map_nil]
  rw [show ((body signalType).instancePorts.ports
      .validStorage).inputs.labels.values = [.value, .enable, .reset] by rfl]
  rw [show ((body signalType).instancePorts.ports
      .dataStorage).inputs.labels.values = [.data, .enable] by rfl]
  rw [show ((body signalType).instancePorts.ports
      .control).inputs.labels.values = [.storedValid, .downstreamReady] by rfl]
  rw [show ((body signalType).instancePorts.ports
      .outputValidOr).inputs.labels.values = [.left, .right] by rfl]
  rw [show ((body signalType).instancePorts.ports
      .outputDataMux).inputs.labels.values = [.select, .whenFalse, .whenTrue] by rfl]
  dsimp [body, context, instancePorts, structuralChildren, wiring,
    sourceDescription, EnabledResetRegister.design, EnabledRegister.design,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [Naming.FifoPorts.ports, Naming.FifoPorts.portsWithNaming,
    Interfaces.Fifo.inputMap, Interfaces.Fifo.outputMap]

set_option maxHeartbeats 1000000 in
private theorem unique (signalType : SignalType) :
    (description signalType).UniqueNames := by
  simp only [description, construction, build, buildResult,
    EnabledResetRegister.placeNamed, EnabledRegister.placeNamed,
    OneEntryFifo.Control.placeNamed, Primitives.Or.placeNamed, Mux.placeNamed,
    EnabledResetRegister.design, EnabledRegister.design,
    Authoring.CircuitDescription.placeNamed,
    Authoring.CircuitDescription.input, Authoring.CircuitDescription.output,
    Authoring.CircuitDescription.wire, Authoring.CircuitDescription.assign,
    Authoring.CircuitDescription.bind_apply,
    Authoring.CircuitDescription.pure_apply]
  simp only [show (inferInstance : Enumeration EnabledResetRegister.Input).values =
      [.value, .enable, .reset] by rfl,
    show (inferInstance : Enumeration EnabledRegister.Input).values =
      [.data, .enable] by rfl,
    show (inferInstance : Enumeration Control.Input).values =
      [.storedValid, .downstreamReady] by rfl,
    show (inferInstance : Enumeration Primitives.BinaryInput).values =
      [.left, .right] by rfl,
    show (inferInstance : Enumeration Mux.Input).values =
      [.select, .whenFalse, .whenTrue] by rfl]
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
  change child ∈ [_, _, _, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal | equal <;>
    subst child <;> constructor <;> exact of_decide_eq_true rfl

theorem corresponds (signalType : SignalType) :
    Corresponds (description signalType) (OneEntryFifo.naming signalType) :=
  ⟨same signalType, unique signalType⟩

end Silean.Modules.OneEntryFifo.Description.Internal
