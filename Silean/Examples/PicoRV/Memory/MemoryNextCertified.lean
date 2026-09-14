import Silean.Examples.PicoRV.Memory.MemoryNext
import Silean.Examples.PicoRV.Memory.MemoryIdleUpdateCertified
import Silean.Examples.PicoRV.Memory.MemoryLookaheadCaptureCertified
import Silean.Examples.PicoRV.Memory.MemoryPhaseDecodeCertified
import Silean.Examples.PicoRV.Memory.MemoryPrefetchedUpdateCertified
import Silean.Examples.PicoRV.Memory.MemoryReadUpdateCertified
import Silean.Examples.PicoRV.Memory.MemoryResetTrapOverrideCertified
import Silean.Examples.PicoRV.Memory.MemoryResponseCaptureCertified
import Silean.Examples.PicoRV.Memory.MemoryWriteUpdateCertified
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified

namespace Silean.Examples.PicoRV.Memory.Next

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  responseCapture := ResponseCapture.certification,
  lookaheadCapture := LookaheadCapture.certification,
  phaseDecode := PhaseDecode.certification,
  idle := IdleUpdate.certification,
  read := ReadUpdate.certification,
  write := WriteUpdate.certification,
  prefetched := PrefetchedUpdate.certification,
  selectWrite := Modules.Mux.certification stateType,
  selectRead := Modules.Mux.certification stateType,
  selectIdle := Modules.Mux.certification stateType,
  resetTrapOverride := ResetTrapOverride.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .currentFields => Modules.NamedTupleSplitter.Rule.apply,
    .responseCapture => ResponseCapture.Rule.apply,
    .lookaheadCapture => StateUpdate.Rule.apply,
    .phaseDecode => PhaseDecode.Rule.apply,
    {.idle, .read, .write, .prefetched} => StateUpdate.Rule.apply,
    .selectWrite => Modules.Mux.Rule.select,
    .selectRead => Modules.Mux.Rule.select,
    .selectIdle => Modules.Mux.Rule.select,
    .resetTrapOverride => ResetTrapOverride.Rule.apply]
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies

  let memoryInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let captured := responseCaptured memoryInputs current
  let lookahead := lookaheadCaptured memoryInputs current captured
  have currentFieldsValue : (proposal.2 .currentFields).outputs = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [Memory.ProofSupport.splitValue_eq_unpack, current] using equation

  have responseValue : (proposal.2 .responseCapture).outputs .state =
      stateMap.pack captured := by
    have equation := (ResponseCapture.outputRule_holds_iff _ _ _).mp
      ((childMatch .responseCapture).1.1 ResponseCapture.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .responseCapture = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current) := by
      funext input
      cases input <;> rfl
    rw [childInputs] at equation
    simpa [ResponseCapture.outputState, memoryInputs, current, captured] using equation
  have lookaheadValue : (proposal.2 .lookaheadCapture).outputs .state =
      stateMap.pack lookahead := by
    have equation := (StateUpdate.outputRule_holds_iff lookaheadCaptured _ _ _).mp
      ((childMatch .lookaheadCapture).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .lookaheadCapture = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack captured) := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using responseValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, memoryInputs, current, captured, lookahead]
      using equation

  have phaseValue : (proposal.2 .phaseDecode).outputs =
      PhaseDecode.outputValues (fun | .mem_state => current .mem_state) := by
    have equation := (PhaseDecode.outputRule_holds_iff _ _ _).mp
      ((childMatch .phaseDecode).1.1 PhaseDecode.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .phaseDecode = (fun | .mem_state => current .mem_state) := by
      funext input
      cases input
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using
        congrFun currentFieldsValue .mem_state
    rw [childInputs] at equation
    exact equation
  have idleFlag : (proposal.2 .phaseDecode).outputs .idle =
      decide (stateNumber current = 0) := by
    rw [phaseValue]
    rfl
  have readFlag : (proposal.2 .phaseDecode).outputs .read =
      decide (stateNumber current = 1) := by
    rw [phaseValue]
    rfl
  have writeFlag : (proposal.2 .phaseDecode).outputs .write =
      decide (stateNumber current = 2) := by
    rw [phaseValue]
    rfl

  have idleValue : (proposal.2 .idle).outputs .state =
      stateMap.pack (idleNextState memoryInputs lookahead) := by
    have equation := (StateUpdate.outputRule_holds_iff
      (fun inputs _ updated => idleNextState inputs updated) _ _ _).mp
      ((childMatch .idle).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .idle = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack lookahead) := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using lookaheadValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, memoryInputs, current, lookahead] using equation
  have readValue : (proposal.2 .read).outputs .state =
      stateMap.pack (readNextState memoryInputs current lookahead) := by
    have equation := (StateUpdate.outputRule_holds_iff readNextState _ _ _).mp
      ((childMatch .read).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .read = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack lookahead) := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using lookaheadValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, memoryInputs, current, lookahead] using equation
  have writeValue : (proposal.2 .write).outputs .state =
      stateMap.pack (writeNextState memoryInputs current lookahead) := by
    have equation := (StateUpdate.outputRule_holds_iff writeNextState _ _ _).mp
      ((childMatch .write).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .write = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack lookahead) := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using lookaheadValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, memoryInputs, current, lookahead] using equation
  have prefetchedValue : (proposal.2 .prefetched).outputs .state =
      stateMap.pack (prefetchedNextState memoryInputs lookahead) := by
    have equation := (StateUpdate.outputRule_holds_iff
      (fun inputs _ updated => prefetchedNextState inputs updated) _ _ _).mp
      ((childMatch .prefetched).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .prefetched = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack lookahead) := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using lookaheadValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, memoryInputs, current, lookahead] using equation

  have writeSelected : (proposal.2 .selectWrite).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .write
        then stateMap.pack (writeNextState memoryInputs current lookahead)
        else stateMap.pack (prefetchedNextState memoryInputs lookahead) := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .selectWrite).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [writeValue, prefetchedValue] at equation
    exact equation
  have readSelected : (proposal.2 .selectRead).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .read
        then stateMap.pack (readNextState memoryInputs current lookahead)
        else (proposal.2 .selectWrite).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .selectRead).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [readValue] at equation
    exact equation
  have idleSelected : (proposal.2 .selectIdle).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .idle
        then stateMap.pack (idleNextState memoryInputs lookahead)
        else (proposal.2 .selectRead).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .selectIdle).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [idleValue] at equation
    exact equation
  have selectedValue : (proposal.2 .selectIdle).outputs .result =
      stateMap.pack (normalNextState memoryInputs current captured) := by
    rw [idleSelected, readSelected, writeSelected, idleFlag, readFlag, writeFlag]
    unfold normalNextState
    change _ = stateMap.pack
      (match stateNumber current with
       | 0 => idleNextState memoryInputs lookahead
       | 1 => readNextState memoryInputs current lookahead
       | 2 => writeNextState memoryInputs current lookahead
       | _ => prefetchedNextState memoryInputs lookahead)
    by_cases idle : stateNumber current = 0
    · simp [idle]
    · simp [idle]
      by_cases read : stateNumber current = 1
      · simp [read]
      · simp [read]
        by_cases write : stateNumber current = 2
        · simp [write]
        · have bound := BitVector.toNat_lt_cardinality 2 (current .mem_state)
          have three : stateNumber current = 3 := by
            have boundFour : BitVector.toNat 2 (current .mem_state) < 4 := by
              simpa [BitVector.cardinality] using bound
            unfold stateNumber at idle read write ⊢
            omega
          simp [three]

  have finalValue : (proposal.2 .resetTrapOverride).outputs .state =
      stateMap.pack (nextState memoryInputs current) := by
    have equation := (ResetTrapOverride.outputRule_holds_iff _ _ _).mp
      ((childMatch .resetTrapOverride).1.1 ResetTrapOverride.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .resetTrapOverride = (fun
          | .inputs => inputs .inputs
          | .captured => stateMap.pack captured
          | .normal => stateMap.pack (normalNextState memoryInputs current captured)) := by
      funext input
      cases input
      · rfl
      · simpa only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using responseValue
      · simpa only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using selectedValue
    rw [childInputs] at equation
    simpa [ResetTrapOverride.outputState, memoryInputs, current, captured,
      nextState] using equation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    rw [show proposal.outputs .state =
        (proposal.2 .resetTrapOverride).outputs .state by exact satisfies.1 .state]
    simpa [outputState, memoryInputs, current] using finalValue
  · rfl

end Certification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Memory.Next
