import Silean.Examples.PicoRV.Control.ControlFetchTransition
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Primitives.Not

namespace Silean.Examples.PicoRV.Control.FetchTransition

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  trueBit := Modules.Constant.certification .bit true,
  wordSize := Modules.Constant.certification (.vector 2 .bit) (twoBitsOfNat 0),
  loadRs1State := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateLdRs1),
  notDecoder := Primitives.notCertified.certification,
  notJalr := Primitives.notCertified.certification,
  commonState := Modules.NamedTupleCombiner.certification stateMap,
  commonFields := Modules.NamedTupleSplitter.certification stateMap,
  jalState := Modules.NamedTupleCombiner.certification stateMap,
  ordinaryState := Modules.NamedTupleCombiner.certification stateMap,
  decodedState := Modules.Mux.certification stateType,
  finalState := Modules.Mux.certification stateType,
  result := Modules.NamedTupleCombiner.certification TransitionValue.signalMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .currentFields, .updatedFields} =>
          Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .trueBit, .wordSize, .loadRs1State} =>
          Primitives.ConstantRule.apply,
        {.notDecoder, .notJalr} => Primitives.NotRule.apply,
        .commonState => Modules.NamedTupleCombiner.Rule.apply,
        .commonFields => Modules.NamedTupleSplitter.Rule.apply,
        {.jalState, .ordinaryState} => Modules.NamedTupleCombiner.Rule.apply,
        .decodedState => Modules.Mux.Rule.select,
        .finalState => Modules.Mux.Rule.select,
        .result => Modules.NamedTupleCombiner.Rule.apply]
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

def commonState (inputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values
  | .cpu_state => updated .cpu_state
  | .latched_store => false
  | .latched_stalu => false
  | .latched_branch => false
  | .latched_is_lu => false
  | .latched_is_lh => false
  | .latched_is_lb => false
  | .latched_rd => inputs.decoded_rd
  | .mem_wordsize => twoBitsOfNat 0
  | .mem_do_prefetch => updated .mem_do_prefetch
  | .mem_do_rinst => !(current .decoder_trigger : Bool)
  | .mem_do_rdata => updated .mem_do_rdata
  | .mem_do_wdata => updated .mem_do_wdata
  | .decoder_trigger => updated .decoder_trigger
  | .decoder_pseudo_trigger => updated .decoder_pseudo_trigger
  | .trap => updated .trap

def jalState (common : stateMap.Values) : stateMap.Values
  | .latched_branch => true
  | .mem_do_rinst => true
  | field => common field

def ordinaryState (inputs : Inputs) (common : stateMap.Values) : stateMap.Values
  | .cpu_state => stateBits cpuStateLdRs1
  | .mem_do_prefetch => !inputs.instr_jalr
  | .mem_do_rinst => false
  | field => common field

def structuralFetchState (inputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values :=
  let common := commonState inputs current updated
  if !(current .decoder_trigger : Bool) then common
  else if inputs.instr_jal then jalState common else ordinaryState inputs common

theorem structuralTransition_eq_fetchTransition (inputs : Inputs)
    (current updated : stateMap.Values) :
    simpleTransition (structuralFetchState inputs current updated) =
      fetchTransition inputs current updated := by
  cases decoder : (current .decoder_trigger : Bool) <;>
    cases jal : inputs.instr_jal <;> cases jalr : inputs.instr_jalr <;>
    simp [structuralFetchState, fetchTransition, simpleTransition,
      decoder, jal, jalr] <;>
    congr <;> funext field <;> cases field <;>
    simp [commonState, jalState, ordinaryState, SignalMap.set,
      decoder, jalr]

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
  let updated := stateMap.unpack (inputs .updated)

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
  have updatedFieldsValue : (proposal.2 .updatedFields).outputs = updated := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [splitValue_eq_unpack, updated] using equation
  have inputField (field : ControlInputs.Field) :
      (proposal.2 .inputsFields).outputs field = controlInputs.toValues field := by
    rw [inputsFieldsValue]
    cases field <;> rfl

  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have trueValue := (Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).1.1 Primitives.ConstantRule.apply)
  have wordSizeValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (twoBitsOfNat 0) _ _ _).mp
    ((childMatch .wordSize).1.1 Primitives.ConstantRule.apply)
  have loadRs1Value := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs1) _ _ _).mp
    ((childMatch .loadRs1State).1.1 Primitives.ConstantRule.apply)
  have notDecoderValue : (proposal.2 .notDecoder).outputs .output =
      !(current .decoder_trigger : Bool) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notDecoder).1.1 Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue] at equation
    exact equation
  have notJalrValue : (proposal.2 .notJalr).outputs .output =
      !controlInputs.instr_jalr := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notJalr).1.1 Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .instr_jalr] at equation
    simpa [Inputs.toValues] using equation

  have commonInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .commonState =
        commonState controlInputs current updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, commonState]
    · simpa using congrFun updatedFieldsValue .cpu_state
    · exact falseValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
    · simpa [Inputs.toValues] using inputField .decoded_rd
    · exact wordSizeValue
    · simpa using congrFun updatedFieldsValue .mem_do_prefetch
    · exact notDecoderValue
    · simpa using congrFun updatedFieldsValue .mem_do_rdata
    · simpa using congrFun updatedFieldsValue .mem_do_wdata
    · simpa using congrFun updatedFieldsValue .decoder_trigger
    · simpa using congrFun updatedFieldsValue .decoder_pseudo_trigger
    · simpa using congrFun updatedFieldsValue .trap
  have commonValue : (proposal.2 .commonState).outputs .value =
      stateMap.pack (commonState controlInputs current updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .commonState).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [commonInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
  have commonFieldsValue : (proposal.2 .commonFields).outputs =
      commonState controlInputs current updated := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .commonFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [commonValue] at equation
    simpa [Modules.NamedTupleSplitter.splitValue_pack] using equation

  have jalInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .jalState =
        jalState (commonState controlInputs current updated) := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, jalState]
    all_goals first | exact trueValue |
      simpa using congrFun commonFieldsValue _
  have jalValue : (proposal.2 .jalState).outputs .value =
      stateMap.pack (jalState (commonState controlInputs current updated)) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .jalState).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [jalInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have ordinaryInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .ordinaryState =
        ordinaryState controlInputs (commonState controlInputs current updated) := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, ordinaryState]
    · exact loadRs1Value
    · simpa using congrFun commonFieldsValue .latched_store
    · simpa using congrFun commonFieldsValue .latched_stalu
    · simpa using congrFun commonFieldsValue .latched_branch
    · simpa using congrFun commonFieldsValue .latched_is_lu
    · simpa using congrFun commonFieldsValue .latched_is_lh
    · simpa using congrFun commonFieldsValue .latched_is_lb
    · simpa using congrFun commonFieldsValue .latched_rd
    · simpa using congrFun commonFieldsValue .mem_wordsize
    · exact notJalrValue
    · exact falseValue
    · simpa using congrFun commonFieldsValue .mem_do_rdata
    · simpa using congrFun commonFieldsValue .mem_do_wdata
    · simpa using congrFun commonFieldsValue .decoder_trigger
    · simpa using congrFun commonFieldsValue .decoder_pseudo_trigger
    · simpa using congrFun commonFieldsValue .trap
  have ordinaryValue : (proposal.2 .ordinaryState).outputs .value =
      stateMap.pack
        (ordinaryState controlInputs (commonState controlInputs current updated)) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .ordinaryState).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [ordinaryInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have decodedValue : (proposal.2 .decodedState).outputs .result =
      stateMap.pack (if controlInputs.instr_jal then
        jalState (commonState controlInputs current updated)
      else ordinaryState controlInputs
        (commonState controlInputs current updated)) := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .decodedState).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .instr_jal, ordinaryValue, jalValue] at equation
    cases jal : controlInputs.instr_jal <;>
      simp [Inputs.toValues, jal] at equation ⊢ <;> exact equation
  have finalValue : (proposal.2 .finalState).outputs .result =
      stateMap.pack (structuralFetchState controlInputs current updated) := by
    have equation := Modules.Mux.result_of_evaluatesTo stateType
      _ _ _ _ (childMatch .finalState).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [notDecoderValue, decodedValue, commonValue] at equation
    cases decoder : (current .decoder_trigger : Bool) <;>
      cases jal : controlInputs.instr_jal <;>
      simp [structuralFetchState, decoder, jal] at equation ⊢ <;> exact equation

  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result =
        (simpleTransition
          (structuralFetchState controlInputs current updated)).toValues := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value,
        Transition.toValues, simpleTransition]
    · exact finalValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
  have resultValue : (proposal.2 .result).outputs .value =
      (simpleTransition
        (structuralFetchState controlInputs current updated)).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .result).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [PhaseTransition.outputRule_holds_iff]
    rw [show proposal.outputs .transition = (proposal.2 .result).outputs .value by
      exact satisfies.1 .transition]
    rw [resultValue, structuralTransition_eq_fetchTransition]
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

end Silean.Examples.PicoRV.Control.FetchTransition
