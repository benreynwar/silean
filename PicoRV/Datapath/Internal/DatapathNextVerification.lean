import PicoRV.Datapath.DatapathNext
import PicoRV.Datapath.Internal.DatapathBaselineVerification
import PicoRV.Datapath.Internal.DatapathExecuteUpdateVerification
import PicoRV.Datapath.Internal.DatapathFetchUpdateVerification
import PicoRV.Datapath.Internal.DatapathLoadRs1UpdateVerification
import PicoRV.Datapath.Internal.DatapathLoadRs2UpdateVerification
import PicoRV.Datapath.Internal.DatapathMemoryUpdateVerification
import PicoRV.Datapath.Internal.DatapathPhaseDecodeVerification
import PicoRV.Datapath.Internal.DatapathResetOverrideVerification
import PicoRV.Datapath.Internal.DatapathShiftUpdateVerification
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace PicoRV.Datapath.Next

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  baseline := Baseline.certification,
  phaseDecode := PhaseDecode.certification,
  fetch := FetchUpdate.certification,
  loadRs1 := LoadRs1Update.certification,
  loadRs2 := LoadRs2Update.certification,
  execute := ExecuteUpdate.certification,
  shift := ShiftUpdate.certification,
  store := StoreUpdate.certification,
  load := LoadUpdate.certification,
  selectLoad := Silean.Modules.Mux.certification stateType,
  selectStore := Silean.Modules.Mux.certification stateType,
  selectShift := Silean.Modules.Mux.certification stateType,
  selectExecute := Silean.Modules.Mux.certification stateType,
  selectLoadRs2 := Silean.Modules.Mux.certification stateType,
  selectLoadRs1 := Silean.Modules.Mux.certification stateType,
  selectFetch := Silean.Modules.Mux.certification stateType,
  resetOverride := ResetOverride.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .inputsFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
    .baseline => Baseline.Rule.apply,
    .phaseDecode => PhaseDecode.Rule.apply,
    {.fetch, .loadRs1, .loadRs2, .execute, .shift, .store, .load} =>
      StateUpdate.Rule.apply,
    .selectLoad => Silean.Modules.Mux.Rule.select,
    .selectStore => Silean.Modules.Mux.Rule.select,
    .selectShift => Silean.Modules.Mux.Rule.select,
    .selectExecute => Silean.Modules.Mux.Rule.select,
    .selectLoadRs2 => Silean.Modules.Mux.Rule.select,
    .selectLoadRs1 => Silean.Modules.Mux.Rule.select,
    .selectFetch => Silean.Modules.Mux.Rule.select,
    .resetOverride => ResetOverride.Rule.apply]
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let datapathInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let baselineState' := baselineState (inputs .alu_out) current
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      DatapathInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have resetnValue : hierStep.childOutputs .inputsFields .resetn =
      datapathInputs.resetn := by rw [inputsFieldsValue]; rfl
  have cpuStateValue : hierStep.childOutputs .inputsFields .cpu_state =
      datapathInputs.cpu_state := by rw [inputsFieldsValue]; rfl

  have baselineValue : hierStep.childOutputs .baseline .state =
      stateMap.pack baselineState' := by
    have equation := (Baseline.outputRule_holds_iff _ _ _).mp
      ((childMatch .baseline).ruleHolds Baseline.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .baseline =
          (fun | .current => inputs .current | .alu_out => inputs .alu_out) := by
      funext input
      cases input <;> rfl
    rw [childInputs] at equation
    simpa [Baseline.outputState, current, baselineState'] using equation

  have decodeValue : hierStep.childOutputs .phaseDecode =
      PhaseDecode.outputValues (fun | .cpu_state => datapathInputs.cpu_state) := by
    have equation := (PhaseDecode.outputRule_holds_iff _ _ _).mp
      ((childMatch .phaseDecode).ruleHolds PhaseDecode.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .phaseDecode =
          (fun | .cpu_state => datapathInputs.cpu_state) := by
      funext input
      cases input
      change hierStep.childOutputs .inputsFields .cpu_state = _
      exact cpuStateValue
    rw [childInputs] at equation
    exact equation
  have decodeFlag (output : PhaseDecode.Output) :
      hierStep.childOutputs .phaseDecode output =
        PhaseDecode.outputValues (fun | .cpu_state => datapathInputs.cpu_state) output :=
    congrFun decodeValue output
  have fetchFlag : hierStep.childOutputs .phaseDecode .fetch =
      decide (stateNumber datapathInputs = cpuStateFetch) := by
    exact decodeFlag .fetch
  have loadRs1Flag : hierStep.childOutputs .phaseDecode .loadRs1 =
      decide (stateNumber datapathInputs = cpuStateLdRs1) := by
    exact decodeFlag .loadRs1
  have loadRs2Flag : hierStep.childOutputs .phaseDecode .loadRs2 =
      decide (stateNumber datapathInputs = cpuStateLdRs2) := by
    exact decodeFlag .loadRs2
  have executeFlag : hierStep.childOutputs .phaseDecode .execute =
      decide (stateNumber datapathInputs = cpuStateExec) := by
    exact decodeFlag .execute
  have shiftFlag : hierStep.childOutputs .phaseDecode .shift =
      decide (stateNumber datapathInputs = cpuStateShift) := by
    exact decodeFlag .shift
  have storeFlag : hierStep.childOutputs .phaseDecode .store =
      decide (stateNumber datapathInputs = cpuStateStmem) := by
    exact decodeFlag .store
  have loadFlag : hierStep.childOutputs .phaseDecode .load =
      decide (stateNumber datapathInputs = cpuStateLdmem) := by
    exact decodeFlag .load

  have fetchValue : hierStep.childOutputs .fetch .state =
      stateMap.pack (fetchNextState datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff fetchNextState _ _ _).mp
      ((childMatch .fetch).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .fetch = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .baseline .state = _
      exact baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have loadRs1Value : hierStep.childOutputs .loadRs1 .state =
      stateMap.pack (loadRs1NextState datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff loadRs1NextState _ _ _).mp
      ((childMatch .loadRs1).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .loadRs1 = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .baseline .state = _
      exact baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have loadRs2Value : hierStep.childOutputs .loadRs2 .state =
      stateMap.pack (loadRs2NextState datapathInputs baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff
      (fun inputs _ updated => loadRs2NextState inputs updated) _ _ _).mp
      ((childMatch .loadRs2).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .loadRs2 = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .baseline .state = _
      exact baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have executeValue : hierStep.childOutputs .execute .state =
      stateMap.pack (executeNextState datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff executeNextState _ _ _).mp
      ((childMatch .execute).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .execute = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .baseline .state = _
      exact baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have shiftValue : hierStep.childOutputs .shift .state =
      stateMap.pack (shiftNextState datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff shiftNextState _ _ _).mp
      ((childMatch .shift).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .shift = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .baseline .state = _
      exact baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have storeValue : hierStep.childOutputs .store .state =
      stateMap.pack (memoryNextState false datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff
      (memoryNextState false) _ _ _).mp
      ((childMatch .store).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .store = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .baseline .state = _
      exact baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have loadValue : hierStep.childOutputs .load .state =
      stateMap.pack (memoryNextState true datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff
      (memoryNextState true) _ _ _).mp
      ((childMatch .load).ruleHolds StateUpdate.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .load = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      change hierStep.childOutputs .baseline .state = _
      exact baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation

  have loadSelected : hierStep.childOutputs .selectLoad .result =
      bif hierStep.childOutputs .phaseDecode .load
        then stateMap.pack (memoryNextState true datapathInputs current baselineState')
        else stateMap.pack baselineState' := by
    have equation := Silean.Modules.Mux.result_of_allowed stateType
      (childMatch .selectLoad).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [loadValue, baselineValue] at equation
    exact equation
  have storeSelected : hierStep.childOutputs .selectStore .result =
      bif hierStep.childOutputs .phaseDecode .store
        then stateMap.pack (memoryNextState false datapathInputs current baselineState')
        else hierStep.childOutputs .selectLoad .result := by
    have equation := Silean.Modules.Mux.result_of_allowed stateType
      (childMatch .selectStore).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [storeValue] at equation
    exact equation
  have shiftSelected : hierStep.childOutputs .selectShift .result =
      bif hierStep.childOutputs .phaseDecode .shift
        then stateMap.pack (shiftNextState datapathInputs current baselineState')
        else hierStep.childOutputs .selectStore .result := by
    have equation := Silean.Modules.Mux.result_of_allowed stateType
      (childMatch .selectShift).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [shiftValue] at equation
    exact equation
  have executeSelected : hierStep.childOutputs .selectExecute .result =
      bif hierStep.childOutputs .phaseDecode .execute
        then stateMap.pack (executeNextState datapathInputs current baselineState')
        else hierStep.childOutputs .selectShift .result := by
    have equation := Silean.Modules.Mux.result_of_allowed stateType
      (childMatch .selectExecute).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [executeValue] at equation
    exact equation
  have loadRs2Selected : hierStep.childOutputs .selectLoadRs2 .result =
      bif hierStep.childOutputs .phaseDecode .loadRs2
        then stateMap.pack (loadRs2NextState datapathInputs baselineState')
        else hierStep.childOutputs .selectExecute .result := by
    have equation := Silean.Modules.Mux.result_of_allowed stateType
      (childMatch .selectLoadRs2).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [loadRs2Value] at equation
    exact equation
  have loadRs1Selected : hierStep.childOutputs .selectLoadRs1 .result =
      bif hierStep.childOutputs .phaseDecode .loadRs1
        then stateMap.pack (loadRs1NextState datapathInputs current baselineState')
        else hierStep.childOutputs .selectLoadRs2 .result := by
    have equation := Silean.Modules.Mux.result_of_allowed stateType
      (childMatch .selectLoadRs1).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [loadRs1Value] at equation
    exact equation
  have fetchSelected : hierStep.childOutputs .selectFetch .result =
      bif hierStep.childOutputs .phaseDecode .fetch
        then stateMap.pack (fetchNextState datapathInputs current baselineState')
        else hierStep.childOutputs .selectLoadRs1 .result := by
    have equation := Silean.Modules.Mux.result_of_allowed stateType
      (childMatch .selectFetch).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [fetchValue] at equation
    exact equation
  have selectedValue : hierStep.childOutputs .selectFetch .result =
      stateMap.pack (normalNextState datapathInputs current baselineState') := by
    rw [fetchSelected, loadRs1Selected, loadRs2Selected, executeSelected,
      shiftSelected, storeSelected, loadSelected]
    rw [fetchFlag, loadRs1Flag, loadRs2Flag, executeFlag, shiftFlag,
      storeFlag, loadFlag]
    unfold normalNextState
    by_cases fetch : stateNumber datapathInputs = cpuStateFetch
    · simp [fetch]
    · simp [fetch]
      by_cases rs1 : stateNumber datapathInputs = cpuStateLdRs1
      · simp [rs1]
      · simp [rs1]
        by_cases rs2 : stateNumber datapathInputs = cpuStateLdRs2
        · simp [rs2]
        · simp [rs2]
          by_cases execute : stateNumber datapathInputs = cpuStateExec
          · simp [execute]
          · simp [execute]
            by_cases shift : stateNumber datapathInputs = cpuStateShift
            · simp [shift]
            · simp [shift]
              by_cases store : stateNumber datapathInputs = cpuStateStmem
              · simp [store]
              · simp [store]
                by_cases load : stateNumber datapathInputs = cpuStateLdmem
                · simp [load]
                · simp [load]

  have resetValue : hierStep.childOutputs .resetOverride .state =
      stateMap.pack (nextStateFromAlu datapathInputs current (inputs .alu_out)) := by
    have equation := (ResetOverride.outputRule_holds_iff _ _ _).mp
      ((childMatch .resetOverride).ruleHolds ResetOverride.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .resetOverride = (fun
          | .resetn => datapathInputs.resetn
          | .selected => stateMap.pack
              (normalNextState datapathInputs current baselineState')) := by
      funext input
      cases input
      · change hierStep.childOutputs .inputsFields .resetn = _
        exact resetnValue
      · change hierStep.childOutputs .selectFetch .result = _
        exact selectedValue
    rw [childInputs] at equation
    simpa [ResetOverride.outputState, nextStateFromAlu, baselineState',
      datapathInputs, current] using equation

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [Next.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state =
        hierStep.childOutputs .resetOverride .state by exact satisfies.1 .state]
    simpa [Next.outputState, datapathInputs, current] using resetValue
  · rfl

end Certification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Datapath.Next
