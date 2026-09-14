import Silean.Examples.PicoRV.Control.ControlResetAndAlignmentOverride
import Silean.Examples.PicoRV.Control.ControlAlignmentCertified
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Control.ResetAndAlignmentOverride

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  baselineFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  fetchState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  trapState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateTrap),
  resetState := Modules.NamedTupleCombiner.certification stateMap,
  resetTransition := Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  notResetn := Primitives.notCertified.certification,
  resetSelection := Modules.Mux.certification transitionType,
  alignment := Alignment.certification,
  anyMisalignment := Primitives.orCertified.certification,
  alignmentEnabled := Primitives.andCertified.certification,
  selectedTransitionFields := Modules.NamedTupleSplitter.certification
    TransitionValue.signalMap,
  selectedStateFields := Modules.NamedTupleSplitter.certification stateMap,
  alignmentState := Modules.NamedTupleCombiner.certification stateMap,
  alignmentTransition := Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  result := Modules.Mux.certification transitionType

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .baselineFields} => Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .fetchState, .trapState} => Primitives.ConstantRule.apply,
        .resetState => Modules.NamedTupleCombiner.Rule.apply,
        .resetTransition => Modules.NamedTupleCombiner.Rule.apply,
        .notResetn => Primitives.NotRule.apply,
        .resetSelection => Modules.Mux.Rule.select,
        .alignment => Alignment.Rule.apply,
        .anyMisalignment => Primitives.OrRule.apply,
        .alignmentEnabled => Primitives.AndRule.apply,
        .selectedTransitionFields => Modules.NamedTupleSplitter.Rule.apply,
        .selectedStateFields => Modules.NamedTupleSplitter.Rule.apply,
        .alignmentState => Modules.NamedTupleCombiner.Rule.apply,
        .alignmentTransition => Modules.NamedTupleCombiner.Rule.apply,
        .result => Modules.Mux.Rule.select]
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
  let baseline := stateMap.unpack (inputs .baseline)
  let selected := Transition.unpack (inputs .selected)

  have inputsFieldsValue : (proposal.2 .inputsFields).outputs =
      ControlInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      ControlInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [splitValue_eq_unpack] using equation
  have baselineFieldsValue : (proposal.2 .baselineFields).outputs = baseline := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .baselineFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [splitValue_eq_unpack, baseline] using equation
  have resetnValue : (proposal.2 .inputsFields).outputs .resetn =
      controlInputs.resetn := by
    rw [inputsFieldsValue]
    rfl
  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have fetchValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
    ((childMatch .fetchState).1.1 Primitives.ConstantRule.apply)
  have trapValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateTrap) _ _ _).mp
    ((childMatch .trapState).1.1 Primitives.ConstantRule.apply)

  have resetStateInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .resetState = (resetTransition baseline).state := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, resetTransition,
        simpleTransition, SignalMap.set]
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
  have resetStateValue : (proposal.2 .resetState).outputs .value =
      stateMap.pack (resetTransition baseline).state := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .resetState).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resetStateInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
  have resetTransitionInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .resetTransition = (resetTransition baseline).toValues := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, Transition.toValues,
        resetTransition, simpleTransition]
    · exact resetStateValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
  have resetTransitionValue : (proposal.2 .resetTransition).outputs .value =
      (resetTransition baseline).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .resetTransition).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resetTransitionInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have notResetnValue : (proposal.2 .notResetn).outputs .output =
      !controlInputs.resetn := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notResetn).1.1 Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [resetnValue] at equation
    exact equation
  have resetSelectionValue : (proposal.2 .resetSelection).outputs .result =
      (resetSelected controlInputs baseline selected).pack := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .resetSelection).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [notResetnValue, resetTransitionValue] at equation
    have selectedPacked : inputs .selected = selected.pack := by
      simp [selected]
    rw [selectedPacked] at equation
    cases reset : (!controlInputs.resetn) <;>
      simp [resetSelected, reset] at equation ⊢ <;> exact equation

  have alignmentValues : (proposal.2 .alignment).outputs =
      Alignment.outputValues
        (fun
          | .inputs => inputs .inputs
          | .current => inputs .current) := by
    have equation := (Alignment.outputRule_holds_iff _ _ _).mp
      ((childMatch .alignment).1.1 Alignment.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have dataValue : (proposal.2 .alignment).outputs .data =
      dataMisaligned controlInputs current := by
    have equation := congrFun alignmentValues Alignment.Output.data
    simpa [Alignment.outputValues, controlInputs, current] using equation
  have instructionValue : (proposal.2 .alignment).outputs .instruction =
      instructionMisaligned controlInputs current := by
    have equation := congrFun alignmentValues Alignment.Output.instruction
    simpa [Alignment.outputValues, controlInputs, current] using equation
  have anyMisalignmentValue : (proposal.2 .anyMisalignment).outputs .output =
      (dataMisaligned controlInputs current ||
        instructionMisaligned controlInputs current) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .anyMisalignment).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [dataValue, instructionValue] at equation
    exact equation
  have alignmentEnabledValue : (proposal.2 .alignmentEnabled).outputs .output =
      (controlInputs.resetn &&
        (dataMisaligned controlInputs current ||
          instructionMisaligned controlInputs current)) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .alignmentEnabled).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [resetnValue, anyMisalignmentValue] at equation
    exact equation

  have selectedTransitionFieldsValue :
      (proposal.2 .selectedTransitionFields).outputs =
        (resetSelected controlInputs baseline selected).toValues := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .selectedTransitionFields).1.1
        Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [resetSelectionValue] at equation
    simpa [Transition.pack] using equation
  have selectedStateFieldsValue : (proposal.2 .selectedStateFields).outputs =
      (resetSelected controlInputs baseline selected).state := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .selectedStateFields).1.1
        Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [selectedTransitionFieldsValue] at equation
    simpa [Transition.toValues, splitValue_eq_unpack] using equation

  let resetChosen := resetSelected controlInputs baseline selected
  have alignmentStateInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .alignmentState =
        stateMap.set resetChosen.state .cpu_state (stateBits cpuStateTrap) := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, SignalMap.set,
        resetChosen]
    · exact trapValue
    all_goals simpa using congrFun selectedStateFieldsValue _
  have alignmentStateValue : (proposal.2 .alignmentState).outputs .value =
      stateMap.pack
        (stateMap.set resetChosen.state .cpu_state (stateBits cpuStateTrap)) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .alignmentState).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [alignmentStateInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
  have alignmentTransitionInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .alignmentTransition =
        (forceTrap resetChosen).toValues := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, Transition.toValues,
        resetChosen, forceTrap]
    · exact alignmentStateValue
    · simpa only [Transition.toValues] using
        congrFun selectedTransitionFieldsValue .setRinst
    · simpa only [Transition.toValues] using
        congrFun selectedTransitionFieldsValue .setRdata
    · simpa only [Transition.toValues] using
        congrFun selectedTransitionFieldsValue .setWdata
  have alignmentTransitionValue :
      (proposal.2 .alignmentTransition).outputs .value =
        (forceTrap resetChosen).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .alignmentTransition).1.1
        Modules.NamedTupleCombiner.Rule.apply)
    rw [alignmentTransitionInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have resultValue : (proposal.2 .result).outputs .result =
      (alignmentOverride controlInputs current resetChosen).pack := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .result).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [alignmentEnabledValue, resetSelectionValue,
      alignmentTransitionValue] at equation
    cases aligned : (controlInputs.resetn &&
        (dataMisaligned controlInputs current ||
          instructionMisaligned controlInputs current)) <;>
      simp [alignmentOverride, resetChosen, aligned] at equation ⊢ <;>
      exact equation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [ResetAndAlignmentOverride.outputRule_holds_iff]
    rw [show proposal.outputs .transition = (proposal.2 .result).outputs .result by
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Control.ResetAndAlignmentOverride
