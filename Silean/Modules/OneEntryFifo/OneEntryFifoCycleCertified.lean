import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EnabledRegister.EnabledRegisterCertified
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterCertified
import Silean.Modules.OneEntryFifo.Control.OneEntryFifoControlCertified
import Silean.Modules.OneEntryFifo.OneEntryFifo
import Silean.Modules.Mux.MuxCertified
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
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType) layerChildren)
      (cycleContract signalType)
      (stateCorresponds signalType layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  let validState : (EnabledResetRegister.cycleContract .bit false).state.Values :=
    fun | .stored => contractState .storedValid
  let dataState : (EnabledRegister.cycleContract signalType).state.Values :=
    fun | .stored => contractState .storedData
  have validCorresponds :
      (layerChildren .validStorage).certification.stateCorresponds
      validState
      (structuralState .validStorage) := corresponds.1
  have dataCorresponds :
      (layerChildren .dataStorage).certification.stateCorresponds
      dataState
      (structuralState .dataStorage) := corresponds.2
  have validMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract layerChildren
    inputs structuralState proposal satisfies .validStorage validState
      validCorresponds
  have dataMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract layerChildren
    inputs structuralState proposal satisfies .dataStorage dataState
      dataCorresponds
  have controlMatches :=
    letI : Subsingleton (childContracts signalType .control).state.Values := by
      change Subsingleton emptySignalMap.Values; infer_instance
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies .control SignalMap.emptyValues
  have validOrMatches :=
    letI : Subsingleton (childContracts signalType .outputValidOr).state.Values := by
      change Subsingleton emptySignalMap.Values; infer_instance
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies .outputValidOr SignalMap.emptyValues
  have muxMatches :=
    letI : Subsingleton (childContracts signalType .outputDataMux).state.Values := by
      change Subsingleton emptySignalMap.Values; infer_instance
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies .outputDataMux SignalMap.emptyValues
  have boundary := satisfies.1
  rcases proposal with ⟨outputs, childValues⟩
  let validInputs := ProposedValues.childInputs (body signalType)
    (fun child => (layerChildren child).moduleStructure) inputs childValues
    Instance.validStorage
  let dataInputs := ProposedValues.childInputs (body signalType)
    (fun child => (layerChildren child).moduleStructure) inputs childValues
    Instance.dataStorage
  let controlInputs := ProposedValues.childInputs (body signalType)
    (fun child => (layerChildren child).moduleStructure) inputs childValues
    Instance.control
  let muxInputs := ProposedValues.childInputs (body signalType)
    (fun child => (layerChildren child).moduleStructure) inputs childValues
    Instance.outputDataMux
  rcases validMatches with ⟨validEvaluates, validNextCorresponds⟩
  rcases dataMatches with ⟨dataEvaluates, dataNextCorresponds⟩
  rcases controlMatches with ⟨controlEvaluates, _⟩
  rcases validOrMatches with ⟨validOrEvaluates, _⟩
  rcases muxMatches with ⟨muxEvaluates, _⟩
  change (EnabledResetRegister.cycleContract .bit false).EvaluatesTo validInputs validState
    (childValues .validStorage).outputs
    ((EnabledResetRegister.cycleContract .bit false).stateRule.apply validInputs validState)
      at validEvaluates
  change (layerChildren .validStorage).certification.stateCorresponds
    ((EnabledResetRegister.cycleContract .bit false).stateRule.apply validInputs validState)
    (childValues .validStorage).nextState at validNextCorresponds
  change (EnabledRegister.cycleContract signalType).EvaluatesTo dataInputs dataState
    (childValues .dataStorage).outputs
    ((EnabledRegister.cycleContract signalType).stateRule.apply dataInputs dataState)
      at dataEvaluates
  change (layerChildren .dataStorage).certification.stateCorresponds
    ((EnabledRegister.cycleContract signalType).stateRule.apply dataInputs dataState)
    (childValues .dataStorage).nextState at dataNextCorresponds
  let validNext := (EnabledResetRegister.cycleContract .bit false).stateRule.apply
    validInputs validState
  let dataNext := (EnabledRegister.cycleContract signalType).stateRule.apply
    dataInputs dataState
  refine ⟨(cycleContract signalType).stateRule.apply inputs contractState, ?_, ?_⟩
  · constructor
    · intro name
      cases name
      · change (forwardRule signalType).Holds inputs contractState _
        rw [forwardRule_holds_iff signalType]
        have validEquation := (EnabledResetRegister.observeRule_holds_iff .bit false _ _ _).mp
          (validEvaluates.1 EnabledResetRegister.Rule.observe)
        have dataEquation := (EnabledRegister.observeRule_holds_iff signalType _ _ _).mp
          (dataEvaluates.1 EnabledRegister.Rule.observe)
        have muxRule := (Mux.selectRule_holds_iff signalType _ _ _).mp
          (muxEvaluates.1 Mux.Rule.select)
        change (childValues .validStorage).outputs .value =
          contractState .storedValid at validEquation
        change (childValues .dataStorage).outputs .q =
          contractState .storedData at dataEquation
        change (childValues .outputDataMux).outputs .result =
          bif muxInputs .select then muxInputs .whenTrue
            else muxInputs .whenFalse at muxRule
        have outputOr := (Primitives.orOutputRule_holds_iff _ _ _).mp
          (validOrEvaluates.1 Primitives.OrRule.apply)
        have validBoundary : outputs .outputValid =
            (childValues .outputValidOr).outputs .output := by
          simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
            EndpointContext.instanceOutput, SignalSource.value] using
              boundary Interfaces.Fifo.Output.outputValid
        have dataBoundary : outputs .outputData =
            (childValues .outputDataMux).outputs .result := by
          simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
            EndpointContext.instanceOutput, SignalSource.value] using
              boundary Interfaces.Fifo.Output.outputData
        have orEquation : (childValues .outputValidOr).outputs .output =
            ((childValues .validStorage).outputs .value || inputs .inputValid) := by
          simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
            EndpointContext.moduleInput, EndpointContext.instanceOutput,
            SignalSource.value] using outputOr
        have muxEquation : (childValues .outputDataMux).outputs .result =
            bif (childValues .validStorage).outputs .value
              then (childValues .dataStorage).outputs .q
              else inputs .inputData := by
          change (childValues .outputDataMux).outputs .result =
            bif (childValues .validStorage).outputs .value
              then (childValues .dataStorage).outputs .q
              else inputs .inputData at muxRule
          exact muxRule
        constructor
        · exact validBoundary.trans (orEquation.trans
            (congrArg (fun value => value || inputs .inputValid) validEquation))
        · rw [validEquation, dataEquation] at muxEquation
          exact dataBoundary.trans muxEquation
      · change (readyRule signalType).Holds inputs contractState _
        rw [readyRule_holds_iff signalType]
        have controlRule := (OneEntryFifo.Control.controlRule_holds_iff _ _ _).mp
          (controlEvaluates.1 OneEntryFifo.Control.Rule.control)
        have validEquation := (EnabledResetRegister.observeRule_holds_iff .bit false _ _ _).mp
          (validEvaluates.1 EnabledResetRegister.Rule.observe)
        change (childValues .validStorage).outputs .value =
          contractState .storedValid at validEquation
        change (childValues .control).outputs .upstreamReady =
            (controlInputs .downstreamReady || !controlInputs .storedValid) ∧
          _ at controlRule
        have readyBoundary : outputs .inputReady =
            (childValues .control).outputs .upstreamReady := by
          simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
            EndpointContext.instanceOutput, SignalSource.value] using
              boundary Interfaces.Fifo.Output.inputReady
        have readyEquation : (childValues .control).outputs .upstreamReady =
            (inputs .outputReady || !(childValues .validStorage).outputs .value) := by
          have downstream : controlInputs .downstreamReady = inputs .outputReady := by
            simp [controlInputs, ProposedValues.childInputs, body, wiring,
              context, instancePorts, EndpointContext.moduleInput,
              EndpointContext.instanceOutput, SignalSource.value]
          have stored : controlInputs .storedValid =
              (childValues .validStorage).outputs .value := by
            simp [controlInputs, ProposedValues.childInputs, body, wiring,
              context, instancePorts, EndpointContext.moduleInput,
              EndpointContext.instanceOutput, SignalSource.value]
          rw [downstream, stored] at controlRule
          exact controlRule.1
        rw [validEquation] at readyEquation
        exact readyBoundary.trans readyEquation
    · rfl
  · have controlRule := (OneEntryFifo.Control.controlRule_holds_iff _ _ _).mp
      (controlEvaluates.1 OneEntryFifo.Control.Rule.control)
    have validOutputRule :=
      (EnabledResetRegister.observeRule_holds_iff .bit false _ _ _).mp
        (validEvaluates.1 EnabledResetRegister.Rule.observe)
    change (childValues .validStorage).outputs .value =
      contractState .storedValid at validOutputRule
    change _ ∧ (childValues .control).outputs .storageUpdate =
      ((controlInputs .downstreamReady && controlInputs .storedValid) ||
        (!controlInputs .downstreamReady && !controlInputs .storedValid)) at controlRule
    have updateEquation := controlRule.2
    change (childValues .control).outputs .storageUpdate =
      ((inputs .outputReady && (childValues .validStorage).outputs .value) ||
        (!inputs .outputReady && !(childValues .validStorage).outputs .value)) at updateEquation
    rw [validOutputRule] at updateEquation
    have validNextEquation : validNext .stored =
        bif validInputs .reset then false
        else bif validInputs .enable then validInputs .value else validState .stored := by
      rfl
    have dataNextEquation : dataNext .stored =
        bif dataInputs .enable then dataInputs .data else dataState .stored := by
      rfl
    let nextValidState : (EnabledResetRegister.cycleContract .bit false).state.Values :=
      fun | .stored => (cycleContract signalType).stateRule.apply inputs contractState .storedValid
    let nextDataState : (EnabledRegister.cycleContract signalType).state.Values :=
      fun | .stored => (cycleContract signalType).stateRule.apply inputs contractState .storedData
    have validNextEq : nextValidState = validNext := by
      funext statePort
      cases statePort
      rw [validNextEquation]
      simp [validInputs, ProposedValues.childInputs, body, wiring, context,
        instancePorts, EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value, validState]
      cases resetValue : inputs .reset
      · simp [nextValidState, cycleContract, cycleBehavior, stateRule_apply_storedValid,
          resetValue]
        exact congrArg
          (fun update => bif update then inputs .inputValid
            else contractState .storedValid) updateEquation.symm
      · simp [nextValidState, cycleContract, cycleBehavior, stateRule_apply_storedValid,
          resetValue]
    have dataNextEq : nextDataState = dataNext := by
      funext statePort
      cases statePort
      rw [dataNextEquation]
      simp [dataInputs, ProposedValues.childInputs, body, wiring, context,
        instancePorts, EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value, dataState]
      exact congrArg
        (fun update => bif update then inputs .inputData
          else contractState .storedData) updateEquation.symm
    change (layerChildren .validStorage).certification.stateCorresponds
        nextValidState
        (childValues .validStorage).nextState ∧
      (layerChildren .dataStorage).certification.stateCorresponds
        nextDataState
        (childValues .dataStorage).nextState
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
