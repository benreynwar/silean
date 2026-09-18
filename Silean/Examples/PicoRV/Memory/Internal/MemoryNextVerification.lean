import Silean.Examples.PicoRV.Memory.MemoryNext
import Silean.Examples.PicoRV.Memory.Internal.MemoryIdleUpdateVerification
import Silean.Examples.PicoRV.Memory.Internal.MemoryLookaheadCaptureVerification
import Silean.Examples.PicoRV.Memory.Internal.MemoryPhaseDecodeVerification
import Silean.Examples.PicoRV.Memory.Internal.MemoryPrefetchedUpdateVerification
import Silean.Examples.PicoRV.Memory.Internal.MemoryReadUpdateVerification
import Silean.Examples.PicoRV.Memory.Internal.MemoryResetTrapOverrideVerification
import Silean.Examples.PicoRV.Memory.Internal.MemoryResponseCaptureVerification
import Silean.Examples.PicoRV.Memory.Internal.MemoryWriteUpdateVerification
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

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
    Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let memoryInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let captured := responseCaptured memoryInputs current
  let lookahead := lookaheadCaptured memoryInputs current captured
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [Memory.ProofSupport.splitValue_eq_unpack, current] using equation

  have responseValue : hierStep.childOutputs .responseCapture .state =
      stateMap.pack captured := by
    have equation := (ResponseCapture.outputRule_holds_iff _ _ _).mp
      ((childMatch .responseCapture).ruleHolds ResponseCapture.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .responseCapture = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current) := by
      funext input
      cases input <;> rfl
    rw [childInputs] at equation
    simpa [ResponseCapture.outputState, memoryInputs, current, captured] using equation
  have lookaheadValue : hierStep.childOutputs .lookaheadCapture .state =
      stateMap.pack lookahead := by
    have equation := (StateUpdate.outputRule_holds_iff lookaheadCaptured _ _ _).mp
      ((childMatch .lookaheadCapture).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .lookaheadCapture = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack captured) := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .responseCapture .state = _
      exact responseValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, memoryInputs, current, captured, lookahead]
      using equation

  have phaseValue : hierStep.childOutputs .phaseDecode =
      PhaseDecode.outputValues (fun | .mem_state => current .mem_state) := by
    have equation := (PhaseDecode.outputRule_holds_iff _ _ _).mp
      ((childMatch .phaseDecode).ruleHolds PhaseDecode.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .phaseDecode = (fun | .mem_state => current .mem_state) := by
      funext input
      cases input
      change hierStep.childOutputs .currentFields .mem_state = _
      exact congrFun currentFieldsValue .mem_state
    rw [childInputs] at equation
    exact equation
  have idleFlag : hierStep.childOutputs .phaseDecode .idle =
      decide (stateNumber current = 0) := by
    rw [phaseValue]
    rfl
  have readFlag : hierStep.childOutputs .phaseDecode .read =
      decide (stateNumber current = 1) := by
    rw [phaseValue]
    rfl
  have writeFlag : hierStep.childOutputs .phaseDecode .write =
      decide (stateNumber current = 2) := by
    rw [phaseValue]
    rfl

  have idleValue : hierStep.childOutputs .idle .state =
      stateMap.pack (idleNextState memoryInputs lookahead) := by
    have equation := (StateUpdate.outputRule_holds_iff
      (fun inputs _ updated => idleNextState inputs updated) _ _ _).mp
      ((childMatch .idle).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .idle = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack lookahead) := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .lookaheadCapture .state = _
      exact lookaheadValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, memoryInputs, current, lookahead] using equation
  have readValue : hierStep.childOutputs .read .state =
      stateMap.pack (readNextState memoryInputs current lookahead) := by
    have equation := (StateUpdate.outputRule_holds_iff readNextState _ _ _).mp
      ((childMatch .read).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .read = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack lookahead) := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .lookaheadCapture .state = _
      exact lookaheadValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, memoryInputs, current, lookahead] using equation
  have writeValue : hierStep.childOutputs .write .state =
      stateMap.pack (writeNextState memoryInputs current lookahead) := by
    have equation := (StateUpdate.outputRule_holds_iff writeNextState _ _ _).mp
      ((childMatch .write).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .write = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack lookahead) := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .lookaheadCapture .state = _
      exact lookaheadValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, memoryInputs, current, lookahead] using equation
  have prefetchedValue : hierStep.childOutputs .prefetched .state =
      stateMap.pack (prefetchedNextState memoryInputs lookahead) := by
    have equation := (StateUpdate.outputRule_holds_iff
      (fun inputs _ updated => prefetchedNextState inputs updated) _ _ _).mp
      ((childMatch .prefetched).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .prefetched = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack lookahead) := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .lookaheadCapture .state = _
      exact lookaheadValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, memoryInputs, current, lookahead] using equation

  have writeSelected : hierStep.childOutputs .selectWrite .result =
      bif hierStep.childOutputs .phaseDecode .write
        then stateMap.pack (writeNextState memoryInputs current lookahead)
        else stateMap.pack (prefetchedNextState memoryInputs lookahead) := by
    have equation := Modules.Mux.result_of_allowed stateType
      (childMatch .selectWrite).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [writeValue, prefetchedValue] at equation
    exact equation
  have readSelected : hierStep.childOutputs .selectRead .result =
      bif hierStep.childOutputs .phaseDecode .read
        then stateMap.pack (readNextState memoryInputs current lookahead)
        else hierStep.childOutputs .selectWrite .result := by
    have equation := Modules.Mux.result_of_allowed stateType
      (childMatch .selectRead).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [readValue] at equation
    exact equation
  have idleSelected : hierStep.childOutputs .selectIdle .result =
      bif hierStep.childOutputs .phaseDecode .idle
        then stateMap.pack (idleNextState memoryInputs lookahead)
        else hierStep.childOutputs .selectRead .result := by
    have equation := Modules.Mux.result_of_allowed stateType
      (childMatch .selectIdle).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [idleValue] at equation
    exact equation
  have selectedValue : hierStep.childOutputs .selectIdle .result =
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

  have finalValue : hierStep.childOutputs .resetTrapOverride .state =
      stateMap.pack (nextState memoryInputs current) := by
    have equation := (ResetTrapOverride.outputRule_holds_iff _ _ _).mp
      ((childMatch .resetTrapOverride).ruleHolds ResetTrapOverride.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .resetTrapOverride = (fun
          | .inputs => inputs .inputs
          | .captured => stateMap.pack captured
          | .normal => stateMap.pack (normalNextState memoryInputs current captured)) := by
      funext input
      cases input
      · rfl
      · change hierStep.childOutputs .responseCapture .state = _
        exact responseValue
      · change hierStep.childOutputs .selectIdle .result = _
        exact selectedValue
    rw [childInputs] at equation
    simpa [ResetTrapOverride.outputState, memoryInputs, current, captured,
      nextState] using equation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state =
        hierStep.childOutputs .resetTrapOverride .state by exact satisfies.1 .state]
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

end Silean.Examples.PicoRV.Memory.Next
