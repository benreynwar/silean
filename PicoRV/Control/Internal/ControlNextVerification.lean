import PicoRV.Control.ControlNext
import PicoRV.Control.Internal.ControlBaselineVerification
import PicoRV.Control.Internal.ControlCommandFinishVerification
import PicoRV.Control.Internal.ControlExecuteTransitionVerification
import PicoRV.Control.Internal.ControlFetchTransitionVerification
import PicoRV.Control.Internal.ControlLoadTransitionVerification
import PicoRV.Control.Internal.ControlLoadRs1TransitionVerification
import PicoRV.Control.Internal.ControlLoadRs2TransitionVerification
import PicoRV.Control.Internal.ControlPhaseDecodeVerification
import PicoRV.Control.Internal.ControlResetAndAlignmentOverrideVerification
import PicoRV.Control.Internal.ControlStoreTransitionVerification
import PicoRV.Control.Internal.ControlShiftTransitionVerification
import PicoRV.Control.Internal.ControlTrapTransitionVerification
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace PicoRV.Control.ControlNext

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Silean.Modules.Constant.certification .bit false,
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
  defaultTransition := Silean.Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  selectLoad := Silean.Modules.Mux.certification transitionType,
  selectStore := Silean.Modules.Mux.certification transitionType,
  selectShift := Silean.Modules.Mux.certification transitionType,
  selectExecute := Silean.Modules.Mux.certification transitionType,
  selectLoadRs2 := Silean.Modules.Mux.certification transitionType,
  selectLoadRs1 := Silean.Modules.Mux.certification transitionType,
  selectFetch := Silean.Modules.Mux.certification transitionType,
  selectTrap := Silean.Modules.Mux.certification transitionType,
  override := ResetAndAlignmentOverride.certification,
  notResetn := Silean.Primitives.notCertified.certification,
  clearCommands := Silean.Primitives.orCertified.certification,
  commandFinish := CommandFinish.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .currentFields} => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .falseBit => Silean.Primitives.ConstantRule.apply,
        .baseline => Baseline.Rule.apply,
        .phaseDecode => PhaseDecode.Rule.apply,
        {.trap, .fetch, .loadRs1, .loadRs2, .execute, .shift, .store, .load} =>
          PhaseTransition.Rule.apply,
        .defaultTransition => Silean.Modules.NamedTupleCombiner.Rule.apply,
        .selectLoad => Silean.Modules.Mux.Rule.select,
        .selectStore => Silean.Modules.Mux.Rule.select,
        .selectShift => Silean.Modules.Mux.Rule.select,
        .selectExecute => Silean.Modules.Mux.Rule.select,
        .selectLoadRs2 => Silean.Modules.Mux.Rule.select,
        .selectLoadRs1 => Silean.Modules.Mux.Rule.select,
        .selectFetch => Silean.Modules.Mux.Rule.select,
        .selectTrap => Silean.Modules.Mux.Rule.select,
        .override => ResetAndAlignmentOverride.Rule.apply,
        .notResetn => Silean.Primitives.NotRule.apply,
        .clearCommands => Silean.Primitives.OrRule.apply,
        .commandFinish => CommandFinish.Rule.apply]
  state := []

private theorem splitValue_eq_unpack (signals : Silean.SignalMap.{0})
    (value : signals.tupleType.Denote) :
    Silean.Modules.NamedTupleSplitter.splitValue signals value = signals.unpack value := by
  calc
    Silean.Modules.NamedTupleSplitter.splitValue signals value =
        Silean.Modules.NamedTupleSplitter.splitValue signals
          (signals.pack (signals.unpack value)) := by rw [signals.pack_unpack]
    _ = signals.unpack value :=
      Silean.Modules.NamedTupleSplitter.splitValue_pack signals _

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Silean.Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies

  let controlInputs := Inputs.unpack (hierStep.inputs .inputs)
  let current := stateMap.unpack (hierStep.inputs .current)
  let baselineState' := baselineState controlInputs current

  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      ControlInputs.signalMap.unpack (hierStep.inputs .inputs) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      ControlInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .inputsFields =
      Silean.Modules.NamedTupleSplitter.splitValue ControlInputs.signalMap
        (hierStep.inputs .inputs) at equation
    exact equation.trans (splitValue_eq_unpack _ _)
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .currentFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .current) at equation
    exact equation.trans ((splitValue_eq_unpack _ _).trans (by rfl))
  have resetnValue : hierStep.childOutputs .inputsFields .resetn =
      controlInputs.resetn := by rw [inputsFieldsValue]; rfl
  have memDoneValue : hierStep.childOutputs .inputsFields .mem_done =
      controlInputs.mem_done := by rw [inputsFieldsValue]; rfl
  have falseValue := (Silean.Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Silean.Primitives.ConstantRule.apply)

  have baselineValue : hierStep.childOutputs .baseline .state =
      stateMap.pack baselineState' := by
    have equation := (Baseline.outputRule_holds_iff _ _ _).mp
      ((childMatch .baseline).ruleHolds Baseline.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
        hierStep.childOutputs .baseline =
          (fun
            | .inputs => hierStep.inputs .inputs
            | .current => hierStep.inputs .current) := by
      funext input
      cases input <;> rfl
    rw [childInputs] at equation
    simpa [Baseline.outputState, controlInputs, current, baselineState'] using equation
  have baselineUnpacked :
      stateMap.unpack (hierStep.childOutputs .baseline .state) = baselineState' :=
    (congrArg stateMap.unpack baselineValue).trans (stateMap.unpack_pack _)

  have decodeValue : hierStep.childOutputs .phaseDecode =
      PhaseDecode.outputValues (fun | .cpu_state => current .cpu_state) := by
    have equation := (PhaseDecode.outputRule_holds_iff _ _ _).mp
      ((childMatch .phaseDecode).ruleHolds PhaseDecode.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
        hierStep.childOutputs .phaseDecode =
          (fun | .cpu_state => current .cpu_state) := by
      funext input
      cases input
      change hierStep.childOutputs .currentFields .cpu_state =
        current .cpu_state
      exact congrFun currentFieldsValue .cpu_state
    rw [childInputs] at equation
    exact equation
  have decodeFlag (output : PhaseDecode.Output) :
      hierStep.childOutputs .phaseDecode output =
        PhaseDecode.outputValues (fun | .cpu_state => current .cpu_state) output :=
    congrFun decodeValue output
  have trapFlag : hierStep.childOutputs .phaseDecode .trap =
      decide (phase current = cpuStateTrap) := by
    have result := decodeFlag .trap
    change hierStep.childOutputs .phaseDecode .trap =
      decide (Silean.BitVector.toNat 8 (current .cpu_state) = cpuStateTrap) at result
    exact result
  have fetchFlag : hierStep.childOutputs .phaseDecode .fetch =
      decide (phase current = cpuStateFetch) := by
    have result := decodeFlag .fetch
    change hierStep.childOutputs .phaseDecode .fetch =
      decide (Silean.BitVector.toNat 8 (current .cpu_state) = cpuStateFetch) at result
    exact result
  have loadRs1Flag : hierStep.childOutputs .phaseDecode .loadRs1 =
      decide (phase current = cpuStateLdRs1) := by
    have result := decodeFlag .loadRs1
    change hierStep.childOutputs .phaseDecode .loadRs1 =
      decide (Silean.BitVector.toNat 8 (current .cpu_state) = cpuStateLdRs1) at result
    exact result
  have loadRs2Flag : hierStep.childOutputs .phaseDecode .loadRs2 =
      decide (phase current = cpuStateLdRs2) := by
    have result := decodeFlag .loadRs2
    change hierStep.childOutputs .phaseDecode .loadRs2 =
      decide (Silean.BitVector.toNat 8 (current .cpu_state) = cpuStateLdRs2) at result
    exact result
  have executeFlag : hierStep.childOutputs .phaseDecode .execute =
      decide (phase current = cpuStateExec) := by
    have result := decodeFlag .execute
    change hierStep.childOutputs .phaseDecode .execute =
      decide (Silean.BitVector.toNat 8 (current .cpu_state) = cpuStateExec) at result
    exact result
  have shiftFlag : hierStep.childOutputs .phaseDecode .shift =
      decide (phase current = cpuStateShift) := by
    have result := decodeFlag .shift
    change hierStep.childOutputs .phaseDecode .shift =
      decide (Silean.BitVector.toNat 8 (current .cpu_state) = cpuStateShift) at result
    exact result
  have storeFlag : hierStep.childOutputs .phaseDecode .store =
      decide (phase current = cpuStateStmem) := by
    have result := decodeFlag .store
    change hierStep.childOutputs .phaseDecode .store =
      decide (Silean.BitVector.toNat 8 (current .cpu_state) = cpuStateStmem) at result
    exact result
  have loadFlag : hierStep.childOutputs .phaseDecode .load =
      decide (phase current = cpuStateLdmem) := by
    have result := decodeFlag .load
    change hierStep.childOutputs .phaseDecode .load =
      decide (Silean.BitVector.toNat 8 (current .cpu_state) = cpuStateLdmem) at result
    exact result

  have trapValue : hierStep.childOutputs .trap .transition =
      (trapTransitionChild controlInputs current baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      trapTransitionChild _ _ _).mp
      ((childMatch .trap).ruleHolds PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun updated => (trapTransitionChild controlInputs current updated).pack)
      baselineUnpacked)
  have fetchValue : hierStep.childOutputs .fetch .transition =
      (fetchTransition controlInputs current baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      fetchTransition _ _ _).mp
      ((childMatch .fetch).ruleHolds PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun updated => (fetchTransition controlInputs current updated).pack)
      baselineUnpacked)
  have loadRs1Value : hierStep.childOutputs .loadRs1 .transition =
      (loadRs1Transition controlInputs baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      (fun inputs _ updated => loadRs1Transition inputs updated) _ _ _).mp
      ((childMatch .loadRs1).ruleHolds PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun updated => (loadRs1Transition controlInputs updated).pack)
      baselineUnpacked)
  have loadRs2Value : hierStep.childOutputs .loadRs2 .transition =
      (loadRs2Transition controlInputs baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      (fun inputs _ updated => loadRs2Transition inputs updated) _ _ _).mp
      ((childMatch .loadRs2).ruleHolds PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun updated => (loadRs2Transition controlInputs updated).pack)
      baselineUnpacked)
  have executeValue : hierStep.childOutputs .execute .transition =
      (executeTransition controlInputs baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      (fun inputs _ updated => executeTransition inputs updated) _ _ _).mp
      ((childMatch .execute).ruleHolds PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun updated => (executeTransition controlInputs updated).pack)
      baselineUnpacked)
  have shiftValue : hierStep.childOutputs .shift .transition =
      (shiftTransition controlInputs baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      (fun inputs _ updated => shiftTransition inputs updated) _ _ _).mp
      ((childMatch .shift).ruleHolds PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun updated => (shiftTransition controlInputs updated).pack)
      baselineUnpacked)
  have storeValue : hierStep.childOutputs .store .transition =
      (storeTransition controlInputs current baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      storeTransition _ _ _).mp
      ((childMatch .store).ruleHolds PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun updated => (storeTransition controlInputs current updated).pack)
      baselineUnpacked)
  have loadValue : hierStep.childOutputs .load .transition =
      (loadTransition controlInputs current baselineState').pack := by
    have equation := (PhaseTransition.outputRule_holds_iff
      loadTransition _ _ _).mp
      ((childMatch .load).ruleHolds PhaseTransition.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun updated => (loadTransition controlInputs current updated).pack)
      baselineUnpacked)

  have defaultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .defaultTransition =
        (simpleTransition baselineState').toValues := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [Transition.toValues, simpleTransition]
    · exact baselineValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
  have defaultValue : hierStep.childOutputs .defaultTransition .value =
      (simpleTransition baselineState').pack := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .defaultTransition).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [defaultInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have loadSelected : hierStep.childOutputs .selectLoad .result =
      bif hierStep.childOutputs .phaseDecode .load
        then (loadTransition controlInputs current baselineState').pack
        else (simpleTransition baselineState').pack := by
    have equation := Silean.Modules.Mux.result_of_allowed transitionType
      (childMatch .selectLoad).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr (Eq.refl _)
      loadValue defaultValue)
  have storeSelected : hierStep.childOutputs .selectStore .result =
      bif hierStep.childOutputs .phaseDecode .store
        then (storeTransition controlInputs current baselineState').pack
        else hierStep.childOutputs .selectLoad .result := by
    have equation := Silean.Modules.Mux.result_of_allowed transitionType
      (childMatch .selectStore).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr (Eq.refl _)
      storeValue (Eq.refl _))
  have shiftSelected : hierStep.childOutputs .selectShift .result =
      bif hierStep.childOutputs .phaseDecode .shift
        then (shiftTransition controlInputs baselineState').pack
        else hierStep.childOutputs .selectStore .result := by
    have equation := Silean.Modules.Mux.result_of_allowed transitionType
      (childMatch .selectShift).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr (Eq.refl _)
      shiftValue (Eq.refl _))
  have executeSelected : hierStep.childOutputs .selectExecute .result =
      bif hierStep.childOutputs .phaseDecode .execute
        then (executeTransition controlInputs baselineState').pack
        else hierStep.childOutputs .selectShift .result := by
    have equation := Silean.Modules.Mux.result_of_allowed transitionType
      (childMatch .selectExecute).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr (Eq.refl _)
      executeValue (Eq.refl _))
  have loadRs2Selected : hierStep.childOutputs .selectLoadRs2 .result =
      bif hierStep.childOutputs .phaseDecode .loadRs2
        then (loadRs2Transition controlInputs baselineState').pack
        else hierStep.childOutputs .selectExecute .result := by
    have equation := Silean.Modules.Mux.result_of_allowed transitionType
      (childMatch .selectLoadRs2).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr (Eq.refl _)
      loadRs2Value (Eq.refl _))
  have loadRs1Selected : hierStep.childOutputs .selectLoadRs1 .result =
      bif hierStep.childOutputs .phaseDecode .loadRs1
        then (loadRs1Transition controlInputs baselineState').pack
        else hierStep.childOutputs .selectLoadRs2 .result := by
    have equation := Silean.Modules.Mux.result_of_allowed transitionType
      (childMatch .selectLoadRs1).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr (Eq.refl _)
      loadRs1Value (Eq.refl _))
  have fetchSelected : hierStep.childOutputs .selectFetch .result =
      bif hierStep.childOutputs .phaseDecode .fetch
        then (fetchTransition controlInputs current baselineState').pack
        else hierStep.childOutputs .selectLoadRs1 .result := by
    have equation := Silean.Modules.Mux.result_of_allowed transitionType
      (childMatch .selectFetch).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr (Eq.refl _)
      fetchValue (Eq.refl _))
  have trapSelected : hierStep.childOutputs .selectTrap .result =
      bif hierStep.childOutputs .phaseDecode .trap
        then (trapTransitionChild controlInputs current baselineState').pack
        else hierStep.childOutputs .selectFetch .result := by
    have equation := Silean.Modules.Mux.result_of_allowed transitionType
      (childMatch .selectTrap).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr (Eq.refl _)
      trapValue (Eq.refl _))
  have selectedValue : hierStep.childOutputs .selectTrap .result =
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

  have overrideValue : hierStep.childOutputs .override .transition =
      (resetAndAlignmentTransition controlInputs current baselineState'
        (phaseTransition controlInputs current baselineState')).pack := by
    have equation := (ResetAndAlignmentOverride.outputRule_holds_iff _ _ _).mp
      ((childMatch .override).ruleHolds ResetAndAlignmentOverride.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
        hierStep.childOutputs .override =
          (fun
            | .inputs => hierStep.inputs .inputs
            | .current => hierStep.inputs .current
            | .baseline => stateMap.pack baselineState'
            | .selected =>
                (phaseTransition controlInputs current baselineState').pack) := by
      funext input
      cases input
      · rfl
      · rfl
      · change hierStep.childOutputs .baseline .state = _
        exact baselineValue
      · change hierStep.childOutputs .selectTrap .result = _
        exact selectedValue
    have sourceOverride : ResetAndAlignmentOverride.outputTransition
        (fun
          | .inputs => hierStep.inputs .inputs
          | .current => hierStep.inputs .current
          | .baseline => stateMap.pack baselineState'
          | .selected =>
              (phaseTransition controlInputs current baselineState').pack) =
        resetAndAlignmentTransition controlInputs current baselineState'
          (phaseTransition controlInputs current baselineState') := by
      unfold ResetAndAlignmentOverride.outputTransition
      rw [stateMap.unpack_pack, Transition.unpack_pack]
    exact equation.trans (congrArg Transition.pack
      ((congrArg ResetAndAlignmentOverride.outputTransition childInputs).trans
        sourceOverride))
  have notResetnValue : hierStep.childOutputs .notResetn .output =
      !controlInputs.resetn := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notResetn).ruleHolds Silean.Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg Bool.not resetnValue)
  have clearValue : hierStep.childOutputs .clearCommands .output =
      (!controlInputs.resetn || controlInputs.mem_done) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .clearCommands).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.or
      notResetnValue memDoneValue)
  have finishValue : hierStep.childOutputs .commandFinish .state =
      stateMap.pack (nextState controlInputs current) := by
    have equation := (CommandFinish.outputRule_holds_iff _ _ _).mp
      ((childMatch .commandFinish).ruleHolds CommandFinish.Rule.apply)
    have childInputs : body.wiring.childInputValues hierStep.inputs
        hierStep.childOutputs .commandFinish =
          (fun
            | .clear => !controlInputs.resetn || controlInputs.mem_done
            | .transition =>
                (resetAndAlignmentTransition controlInputs current baselineState'
                  (phaseTransition controlInputs current baselineState')).pack) := by
      funext input
      cases input
      · change hierStep.childOutputs .clearCommands .output = _
        exact clearValue
      · change hierStep.childOutputs .override .transition = _
        exact overrideValue
    have sourceResult : CommandFinish.outputState
        (fun
          | .clear => !controlInputs.resetn || controlInputs.mem_done
          | .transition =>
              (resetAndAlignmentTransition controlInputs current baselineState'
                (phaseTransition controlInputs current baselineState')).pack) =
        nextState controlInputs current := by
      unfold CommandFinish.outputState nextState
      rw [Transition.unpack_pack]
    exact equation.trans (congrArg stateMap.pack
      ((congrArg CommandFinish.outputState childInputs).trans sourceResult))

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [ControlNext.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state =
        hierStep.childOutputs .commandFinish .state by exact satisfies.1 .state]
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
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Control.ControlNext
