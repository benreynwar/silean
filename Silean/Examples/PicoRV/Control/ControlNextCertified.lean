import Silean.Examples.PicoRV.Control.ControlNext
import Silean.Examples.PicoRV.Control.ControlBaselineCertified
import Silean.Examples.PicoRV.Control.ControlCommandFinishCertified
import Silean.Examples.PicoRV.Control.ControlExecuteTransitionCertified
import Silean.Examples.PicoRV.Control.ControlFetchTransitionCertified
import Silean.Examples.PicoRV.Control.ControlLoadTransitionCertified
import Silean.Examples.PicoRV.Control.ControlLoadRs1TransitionCertified
import Silean.Examples.PicoRV.Control.ControlLoadRs2TransitionCertified
import Silean.Examples.PicoRV.Control.ControlPhaseDecodeCertified
import Silean.Examples.PicoRV.Control.ControlResetAndAlignmentOverrideCertified
import Silean.Examples.PicoRV.Control.ControlStoreTransitionCertified
import Silean.Examples.PicoRV.Control.ControlShiftTransitionCertified
import Silean.Examples.PicoRV.Control.ControlTrapTransitionCertified
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Control.ControlNext

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  baseline := Baseline.certification,
  phaseDecode := PhaseDecode.certification,
  trap := TrapTransition.certification,
  fetch := FetchTransition.certification,
  loadRs1 := LoadRs1Transition.certification,
  loadRs2 := LoadRs2Transition.certification,
  execute := ExecuteTransition.certification,
  shift := ShiftTransition.certification,
  store := StoreTransition.certification,
  load := LoadTransition.certification,
  defaultTransition := Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  selectLoad := Modules.Mux.certification transitionType,
  selectStore := Modules.Mux.certification transitionType,
  selectShift := Modules.Mux.certification transitionType,
  selectExecute := Modules.Mux.certification transitionType,
  selectLoadRs2 := Modules.Mux.certification transitionType,
  selectLoadRs1 := Modules.Mux.certification transitionType,
  selectFetch := Modules.Mux.certification transitionType,
  selectTrap := Modules.Mux.certification transitionType,
  override := ResetAndAlignmentOverride.certification,
  notResetn := Primitives.notCertified.certification,
  clearCommands := Primitives.orCertified.certification,
  commandFinish := CommandFinish.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .currentFields} => Modules.NamedTupleSplitter.Rule.apply,
        .falseBit => Primitives.ConstantRule.apply,
        .baseline => Baseline.Rule.apply,
        .phaseDecode => PhaseDecode.Rule.apply,
        {.trap, .fetch, .loadRs1, .loadRs2, .execute, .shift, .store, .load} =>
          PhaseTransition.Rule.apply,
        .defaultTransition => Modules.NamedTupleCombiner.Rule.apply,
        .selectLoad => Modules.Mux.Rule.select,
        .selectStore => Modules.Mux.Rule.select,
        .selectShift => Modules.Mux.Rule.select,
        .selectExecute => Modules.Mux.Rule.select,
        .selectLoadRs2 => Modules.Mux.Rule.select,
        .selectLoadRs1 => Modules.Mux.Rule.select,
        .selectFetch => Modules.Mux.Rule.select,
        .selectTrap => Modules.Mux.Rule.select,
        .override => ResetAndAlignmentOverride.Rule.apply,
        .notResetn => Primitives.NotRule.apply,
        .clearCommands => Primitives.OrRule.apply,
        .commandFinish => CommandFinish.Rule.apply]
  state := []

private theorem splitValue_eq_unpack (signals : SignalMap.{0})
    (value : signals.tupleType.Denote) :
    Modules.NamedTupleSplitter.splitValue signals value = signals.unpack value := by
  calc
    Modules.NamedTupleSplitter.splitValue signals value =
        Modules.NamedTupleSplitter.splitValue signals
          (signals.pack (signals.unpack value)) := by rw [signals.pack_unpack]
    _ = signals.unpack value :=
      Modules.NamedTupleSplitter.splitValue_pack signals _

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

  let controlInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let baselineState' := baselineState controlInputs current

  have inputsFieldsValue : (proposal.2 .inputsFields).outputs =
      ControlInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      ControlInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [splitValue_eq_unpack] using equation
  have currentFieldsValue : (proposal.2 .currentFields).outputs = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [splitValue_eq_unpack, current] using equation
  have resetnValue : (proposal.2 .inputsFields).outputs .resetn =
      controlInputs.resetn := by rw [inputsFieldsValue]; rfl
  have memDoneValue : (proposal.2 .inputsFields).outputs .mem_done =
      controlInputs.mem_done := by rw [inputsFieldsValue]; rfl
  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)

  have baselineValue : (proposal.2 .baseline).outputs .state =
      stateMap.pack baselineState' := by
    have equation := (Baseline.outputRule_holds_iff _ _ _).mp
      ((childMatch .baseline).1.1 Baseline.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .baseline =
          (fun | .inputs => inputs .inputs | .current => inputs .current) := by
      funext input
      cases input <;> rfl
    rw [childInputs] at equation
    simpa [Baseline.outputState, controlInputs, current, baselineState'] using equation

  have decodeValue : (proposal.2 .phaseDecode).outputs =
      PhaseDecode.outputValues (fun | .cpu_state => current .cpu_state) := by
    have equation := (PhaseDecode.outputRule_holds_iff _ _ _).mp
      ((childMatch .phaseDecode).1.1 PhaseDecode.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .phaseDecode =
          (fun | .cpu_state => current .cpu_state) := by
      funext input
      cases input
      simpa only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using
        congrFun currentFieldsValue .cpu_state
    rw [childInputs] at equation
    exact equation
  have decodeFlag (output : PhaseDecode.Output) :
      (proposal.2 .phaseDecode).outputs output =
        PhaseDecode.outputValues (fun | .cpu_state => current .cpu_state) output :=
    congrFun decodeValue output
  have trapFlag : (proposal.2 .phaseDecode).outputs .trap =
      decide (phase current = cpuStateTrap) := by
    have result := decodeFlag .trap
    change (proposal.2 .phaseDecode).outputs .trap =
      decide (BitVector.toNat 8 (current .cpu_state) = cpuStateTrap) at result
    exact result
  have fetchFlag : (proposal.2 .phaseDecode).outputs .fetch =
      decide (phase current = cpuStateFetch) := by
    have result := decodeFlag .fetch
    change (proposal.2 .phaseDecode).outputs .fetch =
      decide (BitVector.toNat 8 (current .cpu_state) = cpuStateFetch) at result
    exact result
  have loadRs1Flag : (proposal.2 .phaseDecode).outputs .loadRs1 =
      decide (phase current = cpuStateLdRs1) := by
    have result := decodeFlag .loadRs1
    change (proposal.2 .phaseDecode).outputs .loadRs1 =
      decide (BitVector.toNat 8 (current .cpu_state) = cpuStateLdRs1) at result
    exact result
  have loadRs2Flag : (proposal.2 .phaseDecode).outputs .loadRs2 =
      decide (phase current = cpuStateLdRs2) := by
    have result := decodeFlag .loadRs2
    change (proposal.2 .phaseDecode).outputs .loadRs2 =
      decide (BitVector.toNat 8 (current .cpu_state) = cpuStateLdRs2) at result
    exact result
  have executeFlag : (proposal.2 .phaseDecode).outputs .execute =
      decide (phase current = cpuStateExec) := by
    have result := decodeFlag .execute
    change (proposal.2 .phaseDecode).outputs .execute =
      decide (BitVector.toNat 8 (current .cpu_state) = cpuStateExec) at result
    exact result
  have shiftFlag : (proposal.2 .phaseDecode).outputs .shift =
      decide (phase current = cpuStateShift) := by
    have result := decodeFlag .shift
    change (proposal.2 .phaseDecode).outputs .shift =
      decide (BitVector.toNat 8 (current .cpu_state) = cpuStateShift) at result
    exact result
  have storeFlag : (proposal.2 .phaseDecode).outputs .store =
      decide (phase current = cpuStateStmem) := by
    have result := decodeFlag .store
    change (proposal.2 .phaseDecode).outputs .store =
      decide (BitVector.toNat 8 (current .cpu_state) = cpuStateStmem) at result
    exact result
  have loadFlag : (proposal.2 .phaseDecode).outputs .load =
      decide (phase current = cpuStateLdmem) := by
    have result := decodeFlag .load
    change (proposal.2 .phaseDecode).outputs .load =
      decide (BitVector.toNat 8 (current .cpu_state) = cpuStateLdmem) at result
    exact result

  have trapValue : (proposal.2 .trap).outputs .transition =
      (trapTransitionChild controlInputs current baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      trapTransitionChild _ _ _).mp
      ((childMatch .trap).1.1 PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [baselineValue] at equation
    simpa [controlInputs, current, baselineState'] using equation
  have fetchValue : (proposal.2 .fetch).outputs .transition =
      (fetchTransition controlInputs current baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      fetchTransition _ _ _).mp
      ((childMatch .fetch).1.1 PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [baselineValue] at equation
    simpa [controlInputs, current, baselineState'] using equation
  have loadRs1Value : (proposal.2 .loadRs1).outputs .transition =
      (loadRs1Transition controlInputs baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      (fun inputs _ updated => loadRs1Transition inputs updated) _ _ _).mp
      ((childMatch .loadRs1).1.1 PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [baselineValue] at equation
    simpa [controlInputs, current, baselineState'] using equation
  have loadRs2Value : (proposal.2 .loadRs2).outputs .transition =
      (loadRs2Transition controlInputs baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      (fun inputs _ updated => loadRs2Transition inputs updated) _ _ _).mp
      ((childMatch .loadRs2).1.1 PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [baselineValue] at equation
    simpa [controlInputs, current, baselineState'] using equation
  have executeValue : (proposal.2 .execute).outputs .transition =
      (executeTransition controlInputs baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      (fun inputs _ updated => executeTransition inputs updated) _ _ _).mp
      ((childMatch .execute).1.1 PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [baselineValue] at equation
    simpa [controlInputs, current, baselineState'] using equation
  have shiftValue : (proposal.2 .shift).outputs .transition =
      (shiftTransition controlInputs baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      (fun inputs _ updated => shiftTransition inputs updated) _ _ _).mp
      ((childMatch .shift).1.1 PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [baselineValue] at equation
    simpa [controlInputs, current, baselineState'] using equation
  have storeValue : (proposal.2 .store).outputs .transition =
      (storeTransition controlInputs current baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      storeTransition _ _ _).mp
      ((childMatch .store).1.1 PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [baselineValue] at equation
    simpa [controlInputs, current, baselineState'] using equation
  have loadValue : (proposal.2 .load).outputs .transition =
      (loadTransition controlInputs current baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      loadTransition _ _ _).mp
      ((childMatch .load).1.1 PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [baselineValue] at equation
    simpa [controlInputs, current, baselineState'] using equation

  have defaultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .defaultTransition =
        (simpleTransition baselineState').toValues := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value,
        Transition.toValues, simpleTransition]
    · exact baselineValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
  have defaultValue : (proposal.2 .defaultTransition).outputs .value =
      (simpleTransition baselineState').pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .defaultTransition).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [defaultInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have loadSelected : (proposal.2 .selectLoad).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .load
        then (loadTransition controlInputs current baselineState').pack
        else (simpleTransition baselineState').pack := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .selectLoad).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [loadValue, defaultValue] at equation
    exact equation
  have storeSelected : (proposal.2 .selectStore).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .store
        then (storeTransition controlInputs current baselineState').pack
        else (proposal.2 .selectLoad).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .selectStore).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storeValue] at equation
    exact equation
  have shiftSelected : (proposal.2 .selectShift).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .shift
        then (shiftTransition controlInputs baselineState').pack
        else (proposal.2 .selectStore).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .selectShift).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [shiftValue] at equation
    exact equation
  have executeSelected : (proposal.2 .selectExecute).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .execute
        then (executeTransition controlInputs baselineState').pack
        else (proposal.2 .selectShift).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .selectExecute).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [executeValue] at equation
    exact equation
  have loadRs2Selected : (proposal.2 .selectLoadRs2).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .loadRs2
        then (loadRs2Transition controlInputs baselineState').pack
        else (proposal.2 .selectExecute).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .selectLoadRs2).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [loadRs2Value] at equation
    exact equation
  have loadRs1Selected : (proposal.2 .selectLoadRs1).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .loadRs1
        then (loadRs1Transition controlInputs baselineState').pack
        else (proposal.2 .selectLoadRs2).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .selectLoadRs1).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [loadRs1Value] at equation
    exact equation
  have fetchSelected : (proposal.2 .selectFetch).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .fetch
        then (fetchTransition controlInputs current baselineState').pack
        else (proposal.2 .selectLoadRs1).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .selectFetch).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [fetchValue] at equation
    exact equation
  have trapSelected : (proposal.2 .selectTrap).outputs .result =
      bif (proposal.2 .phaseDecode).outputs .trap
        then (trapTransitionChild controlInputs current baselineState').pack
        else (proposal.2 .selectFetch).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .selectTrap).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [trapValue] at equation
    exact equation
  have selectedValue : (proposal.2 .selectTrap).outputs .result =
      (phaseTransition controlInputs current baselineState').pack := by
    rw [trapSelected, fetchSelected, loadRs1Selected, loadRs2Selected,
      executeSelected, shiftSelected, storeSelected, loadSelected]
    rw [trapFlag, fetchFlag, loadRs1Flag, loadRs2Flag, executeFlag,
      shiftFlag, storeFlag, loadFlag]
    unfold phaseTransition
    by_cases htrap : phase current = cpuStateTrap
    · simp [htrap, trapTransitionChild]
    · simp [htrap]
      by_cases hfetch : phase current = cpuStateFetch
      · simp [hfetch]
      · simp [hfetch]
        by_cases hrs1 : phase current = cpuStateLdRs1
        · simp [hrs1]
        · simp [hrs1]
          by_cases hrs2 : phase current = cpuStateLdRs2
          · simp [hrs2]
          · simp [hrs2]
            by_cases hexec : phase current = cpuStateExec
            · simp [hexec]
            · simp [hexec]
              by_cases hshift : phase current = cpuStateShift
              · simp [hshift]
              · simp [hshift]
                by_cases hstore : phase current = cpuStateStmem
                · simp [hstore]
                · simp [hstore]
                  by_cases hload : phase current = cpuStateLdmem
                  · simp [hload]
                  · simp [hload]

  have overrideValue : (proposal.2 .override).outputs .transition =
      (resetAndAlignmentTransition controlInputs current baselineState'
        (phaseTransition controlInputs current baselineState')).pack := by
    have equation := (ResetAndAlignmentOverride.outputRule_holds_iff _ _ _).mp
      ((childMatch .override).1.1 ResetAndAlignmentOverride.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .override =
          (fun
            | .inputs => inputs .inputs
            | .current => inputs .current
            | .baseline => stateMap.pack baselineState'
            | .selected =>
                (phaseTransition controlInputs current baselineState').pack) := by
      funext input
      cases input
      · rfl
      · rfl
      · simpa only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using baselineValue
      · simpa only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using selectedValue
    rw [childInputs] at equation
    simpa [ResetAndAlignmentOverride.outputTransition, controlInputs, current,
      baselineState'] using equation
  have notResetnValue : (proposal.2 .notResetn).outputs .output =
      !controlInputs.resetn := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notResetn).1.1 Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [resetnValue] at equation
    exact equation
  have clearValue : (proposal.2 .clearCommands).outputs .output =
      (!controlInputs.resetn || controlInputs.mem_done) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .clearCommands).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [notResetnValue, memDoneValue] at equation
    exact equation
  have finishValue : (proposal.2 .commandFinish).outputs .state =
      stateMap.pack (nextState controlInputs current) := by
    have equation := (CommandFinish.outputRule_holds_iff _ _ _).mp
      ((childMatch .commandFinish).1.1 CommandFinish.Rule.apply)
    have childInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .commandFinish =
          (fun
            | .clear => !controlInputs.resetn || controlInputs.mem_done
            | .transition =>
                (resetAndAlignmentTransition controlInputs current baselineState'
                  (phaseTransition controlInputs current baselineState')).pack) := by
      funext input
      cases input
      · simpa only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using clearValue
      · simpa only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using overrideValue
    rw [childInputs] at equation
    simpa [CommandFinish.outputState, nextState, baselineState'] using equation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [ControlNext.outputRule_holds_iff]
    rw [show proposal.outputs .state =
        (proposal.2 .commandFinish).outputs .state by exact satisfies.1 .state]
    simpa [ControlNext.outputState, controlInputs, current] using finishValue
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

end Silean.Examples.PicoRV.Control.ControlNext
