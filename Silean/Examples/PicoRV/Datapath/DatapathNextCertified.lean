import Silean.Examples.PicoRV.Datapath.DatapathNext
import Silean.Examples.PicoRV.Datapath.DatapathBaselineCertified
import Silean.Examples.PicoRV.Datapath.DatapathExecuteUpdateCertified
import Silean.Examples.PicoRV.Datapath.DatapathFetchUpdateCertified
import Silean.Examples.PicoRV.Datapath.DatapathLoadRs1UpdateCertified
import Silean.Examples.PicoRV.Datapath.DatapathLoadRs2UpdateCertified
import Silean.Examples.PicoRV.Datapath.DatapathMemoryUpdateCertified
import Silean.Examples.PicoRV.Datapath.DatapathPhaseDecodeCertified
import Silean.Examples.PicoRV.Datapath.DatapathResetOverrideCertified
import Silean.Examples.PicoRV.Datapath.DatapathShiftUpdateCertified
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified

namespace Silean.Examples.PicoRV.Datapath.Next

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  baseline := Baseline.certification,
  phaseDecode := PhaseDecode.certification,
  fetch := FetchUpdate.certification,
  loadRs1 := LoadRs1Update.certification,
  loadRs2 := LoadRs2Update.certification,
  execute := ExecuteUpdate.certification,
  shift := ShiftUpdate.certification,
  store := StoreUpdate.certification,
  load := LoadUpdate.certification,
  selectLoad := Modules.Mux.certification stateType,
  selectStore := Modules.Mux.certification stateType,
  selectShift := Modules.Mux.certification stateType,
  selectExecute := Modules.Mux.certification stateType,
  selectLoadRs2 := Modules.Mux.certification stateType,
  selectLoadRs1 := Modules.Mux.certification stateType,
  selectFetch := Modules.Mux.certification stateType,
  resetOverride := ResetOverride.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .inputsFields => Modules.NamedTupleSplitter.Rule.apply,
    .baseline => Baseline.Rule.apply,
    .phaseDecode => PhaseDecode.Rule.apply,
    {.fetch, .loadRs1, .loadRs2, .execute, .shift, .store, .load} =>
      StateUpdate.Rule.apply,
    .selectLoad => Modules.Mux.Rule.select,
    .selectStore => Modules.Mux.Rule.select,
    .selectShift => Modules.Mux.Rule.select,
    .selectExecute => Modules.Mux.Rule.select,
    .selectLoadRs2 => Modules.Mux.Rule.select,
    .selectLoadRs1 => Modules.Mux.Rule.select,
    .selectFetch => Modules.Mux.Rule.select,
    .resetOverride => ResetOverride.Rule.apply]
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

  let datapathInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let baselineState' := baselineState (inputs .alu_out) current
  have inputsFieldsValue : (proposal.2 .inputsFields).outputs =
      DatapathInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have resetnValue : (proposal.2 .inputsFields).outputs .resetn =
      datapathInputs.resetn := by rw [inputsFieldsValue]; rfl
  have cpuStateValue : (proposal.2 .inputsFields).outputs .cpu_state =
      datapathInputs.cpu_state := by rw [inputsFieldsValue]; rfl

  have baselineValue : (proposal.2 .baseline).outputs .state =
      stateMap.pack baselineState' := by
    have equation := (Baseline.outputRule_holds_iff _ _ _).mp
      ((childMatch .baseline).1.1 Baseline.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .baseline =
          (fun | .current => inputs .current | .alu_out => inputs .alu_out) := by
      funext input
      cases input <;> rfl
    rw [childInputs] at equation
    simpa [Baseline.outputState, current, baselineState'] using equation

  have decodeValue : (proposal.2 .phaseDecode).outputs =
      PhaseDecode.outputValues (fun | .cpu_state => datapathInputs.cpu_state) := by
    have equation := (PhaseDecode.outputRule_holds_iff _ _ _).mp
      ((childMatch .phaseDecode).1.1 PhaseDecode.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .phaseDecode =
          (fun | .cpu_state => datapathInputs.cpu_state) := by
      funext input
      cases input
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using cpuStateValue
    rw [childInputs] at equation
    exact equation
  have decodeFlag (output : PhaseDecode.Output) :
      (proposal.2 .phaseDecode).outputs output =
        PhaseDecode.outputValues (fun | .cpu_state => datapathInputs.cpu_state) output :=
    congrFun decodeValue output
  have fetchFlag : (proposal.2 .phaseDecode).outputs .fetch =
      decide (stateNumber datapathInputs = cpuStateFetch) := by
    exact decodeFlag .fetch
  have loadRs1Flag : (proposal.2 .phaseDecode).outputs .loadRs1 =
      decide (stateNumber datapathInputs = cpuStateLdRs1) := by
    exact decodeFlag .loadRs1
  have loadRs2Flag : (proposal.2 .phaseDecode).outputs .loadRs2 =
      decide (stateNumber datapathInputs = cpuStateLdRs2) := by
    exact decodeFlag .loadRs2
  have executeFlag : (proposal.2 .phaseDecode).outputs .execute =
      decide (stateNumber datapathInputs = cpuStateExec) := by
    exact decodeFlag .execute
  have shiftFlag : (proposal.2 .phaseDecode).outputs .shift =
      decide (stateNumber datapathInputs = cpuStateShift) := by
    exact decodeFlag .shift
  have storeFlag : (proposal.2 .phaseDecode).outputs .store =
      decide (stateNumber datapathInputs = cpuStateStmem) := by
    exact decodeFlag .store
  have loadFlag : (proposal.2 .phaseDecode).outputs .load =
      decide (stateNumber datapathInputs = cpuStateLdmem) := by
    exact decodeFlag .load

  have fetchValue : (proposal.2 .fetch).outputs .state =
      stateMap.pack (fetchNextState datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff fetchNextState _ _ _).mp
      ((childMatch .fetch).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .fetch = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have loadRs1Value : (proposal.2 .loadRs1).outputs .state =
      stateMap.pack (loadRs1NextState datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff loadRs1NextState _ _ _).mp
      ((childMatch .loadRs1).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .loadRs1 = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have loadRs2Value : (proposal.2 .loadRs2).outputs .state =
      stateMap.pack (loadRs2NextState datapathInputs baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff
      (fun inputs _ updated => loadRs2NextState inputs updated) _ _ _).mp
      ((childMatch .loadRs2).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .loadRs2 = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have executeValue : (proposal.2 .execute).outputs .state =
      stateMap.pack (executeNextState datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff executeNextState _ _ _).mp
      ((childMatch .execute).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .execute = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have shiftValue : (proposal.2 .shift).outputs .state =
      stateMap.pack (shiftNextState datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff shiftNextState _ _ _).mp
      ((childMatch .shift).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .shift = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have storeValue : (proposal.2 .store).outputs .state =
      stateMap.pack (memoryNextState false datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff
      (memoryNextState false) _ _ _).mp
      ((childMatch .store).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .store = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation
  have loadValue : (proposal.2 .load).outputs .state =
      stateMap.pack (memoryNextState true datapathInputs current baselineState') := by
    have equation := (StateUpdate.outputRule_holds_iff
      (memoryNextState true) _ _ _).mp
      ((childMatch .load).1.1 StateUpdate.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .load = (fun
          | .inputs => inputs .inputs
          | .current => inputs .current
          | .updated => stateMap.pack baselineState') := by
      funext input
      cases input <;> try rfl
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using baselineValue
    rw [childInputs] at equation
    simpa [StateUpdate.outputState, datapathInputs, current, baselineState'] using equation

  have loadSelected : (proposal.2 .selectLoad).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .load
        then stateMap.pack (memoryNextState true datapathInputs current baselineState')
        else stateMap.pack baselineState' := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .selectLoad).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [loadValue, baselineValue] at equation
    exact equation
  have storeSelected : (proposal.2 .selectStore).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .store
        then stateMap.pack (memoryNextState false datapathInputs current baselineState')
        else (proposal.2 .selectLoad).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .selectStore).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storeValue] at equation
    exact equation
  have shiftSelected : (proposal.2 .selectShift).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .shift
        then stateMap.pack (shiftNextState datapathInputs current baselineState')
        else (proposal.2 .selectStore).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .selectShift).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [shiftValue] at equation
    exact equation
  have executeSelected : (proposal.2 .selectExecute).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .execute
        then stateMap.pack (executeNextState datapathInputs current baselineState')
        else (proposal.2 .selectShift).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .selectExecute).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [executeValue] at equation
    exact equation
  have loadRs2Selected : (proposal.2 .selectLoadRs2).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .loadRs2
        then stateMap.pack (loadRs2NextState datapathInputs baselineState')
        else (proposal.2 .selectExecute).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .selectLoadRs2).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [loadRs2Value] at equation
    exact equation
  have loadRs1Selected : (proposal.2 .selectLoadRs1).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .loadRs1
        then stateMap.pack (loadRs1NextState datapathInputs current baselineState')
        else (proposal.2 .selectLoadRs2).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .selectLoadRs1).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [loadRs1Value] at equation
    exact equation
  have fetchSelected : (proposal.2 .selectFetch).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .fetch
        then stateMap.pack (fetchNextState datapathInputs current baselineState')
        else (proposal.2 .selectLoadRs1).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .selectFetch).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [fetchValue] at equation
    exact equation
  have selectedValue : (proposal.2 .selectFetch).outputs .result =
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

  have resetValue : (proposal.2 .resetOverride).outputs .state =
      stateMap.pack (nextStateFromAlu datapathInputs current (inputs .alu_out)) := by
    have equation := (ResetOverride.outputRule_holds_iff _ _ _).mp
      ((childMatch .resetOverride).1.1 ResetOverride.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .resetOverride = (fun
          | .resetn => datapathInputs.resetn
          | .selected => stateMap.pack
              (normalNextState datapathInputs current baselineState')) := by
      funext input
      cases input
      · simpa only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using resetnValue
      · simpa only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using selectedValue
    rw [childInputs] at equation
    simpa [ResetOverride.outputState, nextStateFromAlu, baselineState',
      datapathInputs, current] using equation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [Next.outputRule_holds_iff]
    rw [show proposal.outputs .state =
        (proposal.2 .resetOverride).outputs .state by exact satisfies.1 .state]
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Datapath.Next
