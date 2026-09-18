import PicoRV.Control.ControlFetchTransition
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.Not

namespace PicoRV.Control.FetchTransition

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Silean.Modules.Constant.certification .bit false,
  trueBit := Silean.Modules.Constant.certification .bit true,
  wordSize := Silean.Modules.Constant.certification (.vector 2 .bit) (twoBitsOfNat 0),
  loadRs1State := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateLdRs1),
  notDecoder := Silean.Primitives.notCertified.certification,
  notJalr := Silean.Primitives.notCertified.certification,
  commonState := Silean.Modules.NamedTupleCombiner.certification stateMap,
  commonFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  jalState := Silean.Modules.NamedTupleCombiner.certification stateMap,
  ordinaryState := Silean.Modules.NamedTupleCombiner.certification stateMap,
  decodedState := Silean.Modules.Mux.certification stateType,
  finalState := Silean.Modules.Mux.certification stateType,
  result := Silean.Modules.NamedTupleCombiner.certification TransitionValue.signalMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .currentFields, .updatedFields} =>
          Silean.Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .trueBit, .wordSize, .loadRs1State} =>
          Silean.Primitives.ConstantRule.apply,
        {.notDecoder, .notJalr} => Silean.Primitives.NotRule.apply,
        .commonState => Silean.Modules.NamedTupleCombiner.Rule.apply,
        .commonFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        {.jalState, .ordinaryState} => Silean.Modules.NamedTupleCombiner.Rule.apply,
        .decodedState => Silean.Modules.Mux.Rule.select,
        .finalState => Silean.Modules.Mux.Rule.select,
        .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
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
    simp [commonState, jalState, ordinaryState, Silean.SignalMap.set,
      decoder, jalr]

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
  let updated := stateMap.unpack (hierStep.inputs .updated)

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
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .updatedFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .updated) at equation
    exact equation.trans ((splitValue_eq_unpack _ _).trans (by rfl))
  have inputField (field : ControlInputs.Field) :
      hierStep.childOutputs .inputsFields field = controlInputs.toValues field := by
    rw [inputsFieldsValue]
    cases field <;> rfl

  have falseValue := (Silean.Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Silean.Primitives.ConstantRule.apply)
  have trueValue := (Silean.Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).ruleHolds Silean.Primitives.ConstantRule.apply)
  have wordSizeValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (twoBitsOfNat 0) _ _ _).mp
    ((childMatch .wordSize).ruleHolds Silean.Primitives.ConstantRule.apply)
  have loadRs1Value := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdRs1) _ _ _).mp
    ((childMatch .loadRs1State).ruleHolds Silean.Primitives.ConstantRule.apply)
  have notDecoderValue : hierStep.childOutputs .notDecoder .output =
      !(current .decoder_trigger : Bool) := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notDecoder).ruleHolds Silean.Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg Bool.not
      (congrFun currentFieldsValue .decoder_trigger))
  have notJalrValue : hierStep.childOutputs .notJalr .output =
      !controlInputs.instr_jalr := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notJalr).ruleHolds Silean.Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg Bool.not (inputField .instr_jalr))

  have commonInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .commonState =
        commonState controlInputs current updated := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [commonState]
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
  have commonValue : hierStep.childOutputs .commonState .value =
      stateMap.pack (commonState controlInputs current updated) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .commonState).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [commonInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
  have commonFieldsValue : hierStep.childOutputs .commonFields =
      commonState controlInputs current updated := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .commonFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| (congrArg
      (Silean.Modules.NamedTupleSplitter.splitValue stateMap) commonValue).trans
        (Silean.Modules.NamedTupleSplitter.splitValue_pack _ _)

  have jalInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .jalState =
        jalState (commonState controlInputs current updated) := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [jalState]
    all_goals first | exact trueValue |
      simpa using congrFun commonFieldsValue _
  have jalValue : hierStep.childOutputs .jalState .value =
      stateMap.pack (jalState (commonState controlInputs current updated)) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .jalState).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [jalInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have ordinaryInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .ordinaryState =
        ordinaryState controlInputs (commonState controlInputs current updated) := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [ordinaryState]
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
  have ordinaryValue : hierStep.childOutputs .ordinaryState .value =
      stateMap.pack
        (ordinaryState controlInputs (commonState controlInputs current updated)) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .ordinaryState).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [ordinaryInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have decodedValue : hierStep.childOutputs .decodedState .result =
      stateMap.pack (if controlInputs.instr_jal then
        jalState (commonState controlInputs current updated)
      else ordinaryState controlInputs
        (commonState controlInputs current updated)) := by
    have equation := Silean.Modules.Mux.result_of_allowed stateType
      (childMatch .decodedState).allowed
    normalize_child_hyp equation unfolding wiring, context
    have result := equation.trans (bif_congr (inputField .instr_jal)
      jalValue ordinaryValue)
    cases jal : controlInputs.instr_jal <;>
      simp [Inputs.toValues, jal] at result ⊢ <;> exact result
  have finalValue : hierStep.childOutputs .finalState .result =
      stateMap.pack (structuralFetchState controlInputs current updated) := by
    have equation := Silean.Modules.Mux.result_of_allowed stateType
      (childMatch .finalState).allowed
    normalize_child_hyp equation unfolding wiring, context
    have result := equation.trans (bif_congr notDecoderValue
      commonValue decodedValue)
    cases decoder : (current .decoder_trigger : Bool) <;>
      cases jal : controlInputs.instr_jal <;>
      simp [structuralFetchState, decoder, jal] at result ⊢ <;> exact result

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result =
        (simpleTransition
          (structuralFetchState controlInputs current updated)).toValues := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [Transition.toValues, simpleTransition]
    · exact finalValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
  have resultValue : hierStep.childOutputs .result .value =
      (simpleTransition
        (structuralFetchState controlInputs current updated)).pack := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .result).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [PhaseTransition.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .transition = hierStep.childOutputs .result .value by
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
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Control.FetchTransition
