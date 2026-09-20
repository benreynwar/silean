import PicoRV.Control.ControlResetAndAlignmentOverride
import PicoRV.Control.Internal.ControlAlignmentVerification
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace PicoRV.Control.ResetAndAlignmentOverride

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  baselineFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Silean.Modules.Constant.certification .bit false,
  fetchState := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  trapState := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateTrap),
  resetState := Silean.Modules.NamedTupleCombiner.certification stateMap,
  resetTransition := Silean.Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  notResetn := Silean.Primitives.notCertified.certification,
  resetSelection := Silean.Modules.Mux.certification transitionType,
  alignment := Alignment.certification,
  anyMisalignment := Silean.Primitives.orCertified.certification,
  alignmentEnabled := Silean.Primitives.andCertified.certification,
  selectedTransitionFields := Silean.Modules.NamedTupleSplitter.certification
    TransitionValue.signalMap,
  selectedStateFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  alignmentState := Silean.Modules.NamedTupleCombiner.certification stateMap,
  alignmentTransition := Silean.Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  result := Silean.Modules.Mux.certification transitionType

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .baselineFields} => Silean.Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .fetchState, .trapState} => Silean.Primitives.ConstantRule.apply,
        .resetState => Silean.Modules.NamedTupleCombiner.Rule.apply,
        .resetTransition => Silean.Modules.NamedTupleCombiner.Rule.apply,
        .notResetn => Silean.Primitives.NotRule.apply,
        .resetSelection => Silean.Modules.Mux.Rule.select,
        .alignment => Alignment.Rule.apply,
        .anyMisalignment => Silean.Primitives.OrRule.apply,
        .alignmentEnabled => Silean.Primitives.AndRule.apply,
        .selectedTransitionFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .selectedStateFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .alignmentState => Silean.Modules.NamedTupleCombiner.Rule.apply,
        .alignmentTransition => Silean.Modules.NamedTupleCombiner.Rule.apply,
        .result => Silean.Modules.Mux.Rule.select]
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

def resetSelected (inputs : Inputs) (baseline : stateMap.Values)
    (selected : Transition) : Transition :=
  if !inputs.resetn then resetTransition baseline else selected

def forceTrap (selected : Transition) : Transition :=
  { selected with state :=
      stateMap.set selected.state .cpu_state (stateBits cpuStateTrap) }

def alignmentOverride (inputs : Inputs) (current : stateMap.Values)
    (selected : Transition) : Transition :=
  if inputs.resetn &&
      (dataMisaligned inputs current || instructionMisaligned inputs current) then
    forceTrap selected
  else selected

theorem alignmentOverride_resetSelected_eq_contract
    (inputs : Inputs) (current baseline : stateMap.Values)
    (selected : Transition) :
    alignmentOverride inputs current (resetSelected inputs baseline selected) =
      resetAndAlignmentTransition inputs current baseline selected := by
  rfl

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
  let baseline := stateMap.unpack (hierStep.inputs .baseline)
  let selected := Transition.unpack (hierStep.inputs .selected)

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
  have baselineFieldsValue : hierStep.childOutputs .baselineFields = baseline := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .baselineFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .baselineFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .baseline) at equation
    exact equation.trans ((splitValue_eq_unpack _ _).trans (by rfl))
  have resetnValue : hierStep.childOutputs .inputsFields .resetn =
      controlInputs.resetn := by
    rw [inputsFieldsValue]
    rfl
  have falseValue := Silean.Modules.Constant.output_of_allowed .bit false
    (childMatch .falseBit).allowed
  have fetchValue := Silean.Modules.Constant.output_of_allowed
    (.vector 8 .bit) (stateBits cpuStateFetch)
    (childMatch .fetchState).allowed
  have trapValue := Silean.Modules.Constant.output_of_allowed
    (.vector 8 .bit) (stateBits cpuStateTrap)
    (childMatch .trapState).allowed

  have resetStateInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .resetState = (resetTransition baseline).state := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [resetTransition, simpleTransition, Silean.SignalMap.set]
    · exact fetchValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
    · simpa using congrFun baselineFieldsValue .latched_rd
    · simpa using congrFun baselineFieldsValue .mem_wordsize
    · simpa using congrFun baselineFieldsValue .mem_do_prefetch
    · simpa using congrFun baselineFieldsValue .mem_do_rinst
    · simpa using congrFun baselineFieldsValue .mem_do_rdata
    · simpa using congrFun baselineFieldsValue .mem_do_wdata
    · simpa using congrFun baselineFieldsValue .decoder_trigger
    · simpa using congrFun baselineFieldsValue .decoder_pseudo_trigger
    · simpa using congrFun baselineFieldsValue .trap
  have resetStateValue : hierStep.childOutputs .resetState .value =
      stateMap.pack (resetTransition baseline).state := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .resetState).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resetStateInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
  have resetTransitionInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .resetTransition = (resetTransition baseline).toValues := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [Transition.toValues, resetTransition, simpleTransition]
    · exact resetStateValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
  have resetTransitionValue : hierStep.childOutputs .resetTransition .value =
      (resetTransition baseline).pack := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .resetTransition).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resetTransitionInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have notResetnValue : hierStep.childOutputs .notResetn .output =
      !controlInputs.resetn := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notResetn).ruleHolds Silean.Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg Bool.not resetnValue)
  have resetSelectionValue : hierStep.childOutputs .resetSelection .result =
      (resetSelected controlInputs baseline selected).pack := by
    have equation := Silean.Modules.Mux.result_of_allowed transitionType
      (childMatch .resetSelection).allowed
    normalize_child_hyp equation unfolding wiring, context
    have selectedPacked : hierStep.inputs .selected = selected.pack := by
      simp [selected]
    have result := equation.trans (bif_congr notResetnValue
      resetTransitionValue selectedPacked)
    cases reset : (!controlInputs.resetn) <;>
      simp [resetSelected, reset] at result ⊢ <;> exact result

  have alignmentValues : hierStep.childOutputs .alignment =
      Alignment.outputValues
        (fun
          | .inputs => hierStep.inputs .inputs
          | .current => hierStep.inputs .current) := by
    have equation := (Alignment.outputRule_holds_iff _ _ _).mp
      ((childMatch .alignment).ruleHolds Alignment.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have dataValue : hierStep.childOutputs .alignment .data =
      dataMisaligned controlInputs current := by
    have equation := congrFun alignmentValues Alignment.Output.data
    simpa [Alignment.outputValues, controlInputs, current] using equation
  have instructionValue : hierStep.childOutputs .alignment .instruction =
      instructionMisaligned controlInputs current := by
    have equation := congrFun alignmentValues Alignment.Output.instruction
    simpa [Alignment.outputValues, controlInputs, current] using equation
  have anyMisalignmentValue : hierStep.childOutputs .anyMisalignment .output =
      (dataMisaligned controlInputs current ||
        instructionMisaligned controlInputs current) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .anyMisalignment).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.or dataValue instructionValue)
  have alignmentEnabledValue : hierStep.childOutputs .alignmentEnabled .output =
      (controlInputs.resetn &&
        (dataMisaligned controlInputs current ||
          instructionMisaligned controlInputs current)) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .alignmentEnabled).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and
      resetnValue anyMisalignmentValue)

  have selectedTransitionFieldsValue :
      hierStep.childOutputs .selectedTransitionFields =
        (resetSelected controlInputs baseline selected).toValues := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .selectedTransitionFields).ruleHolds
        Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| (congrArg
      (Silean.Modules.NamedTupleSplitter.splitValue TransitionValue.signalMap)
      resetSelectionValue).trans (by
        simp [Transition.pack,
          Silean.Modules.NamedTupleSplitter.splitValue_pack])
  have selectedStateFieldsValue : hierStep.childOutputs .selectedStateFields =
      (resetSelected controlInputs baseline selected).state := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .selectedStateFields).ruleHolds
        Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| (congrArg
      (Silean.Modules.NamedTupleSplitter.splitValue stateMap)
      (congrFun selectedTransitionFieldsValue .state)).trans (by
        simp [Transition.toValues,
          Silean.Modules.NamedTupleSplitter.splitValue_pack])

  let resetChosen := resetSelected controlInputs baseline selected
  have alignmentStateInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .alignmentState =
        stateMap.set resetChosen.state .cpu_state (stateBits cpuStateTrap) := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [Silean.SignalMap.set, resetChosen]
    · exact trapValue
    all_goals simpa using congrFun selectedStateFieldsValue _
  have alignmentStateValue : hierStep.childOutputs .alignmentState .value =
      stateMap.pack
        (stateMap.set resetChosen.state .cpu_state (stateBits cpuStateTrap)) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .alignmentState).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [alignmentStateInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
  have alignmentTransitionInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .alignmentTransition =
        (forceTrap resetChosen).toValues := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [Transition.toValues, resetChosen, forceTrap]
    · exact alignmentStateValue
    · simpa only [Transition.toValues] using
        congrFun selectedTransitionFieldsValue .setRinst
    · simpa only [Transition.toValues] using
        congrFun selectedTransitionFieldsValue .setRdata
    · simpa only [Transition.toValues] using
        congrFun selectedTransitionFieldsValue .setWdata
  have alignmentTransitionValue :
      hierStep.childOutputs .alignmentTransition .value =
        (forceTrap resetChosen).pack := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .alignmentTransition).ruleHolds
        Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [alignmentTransitionInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have resultValue : hierStep.childOutputs .result .result =
      (alignmentOverride controlInputs current resetChosen).pack := by
    have equation := Silean.Modules.Mux.result_of_allowed transitionType
      (childMatch .result).allowed
    normalize_child_hyp equation unfolding wiring, context
    have result := equation.trans (bif_congr alignmentEnabledValue
      alignmentTransitionValue resetSelectionValue)
    cases aligned : (controlInputs.resetn &&
        (dataMisaligned controlInputs current ||
          instructionMisaligned controlInputs current)) <;>
      simp [alignmentOverride, resetChosen, aligned] at result ⊢ <;>
      exact result

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [ResetAndAlignmentOverride.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .transition = hierStep.childOutputs .result .result by
      exact satisfies.1 .transition]
    rw [resultValue, alignmentOverride_resetSelected_eq_contract]
    rfl
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

end PicoRV.Control.ResetAndAlignmentOverride
