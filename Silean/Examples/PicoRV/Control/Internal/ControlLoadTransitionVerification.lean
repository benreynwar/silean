import Silean.Examples.PicoRV.Control.ControlLoadTransition
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMuxTheorems
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Control.LoadTransition

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  trueBit := Modules.Constant.certification .bit true,
  sizeWord := Modules.Constant.certification (.vector 2 .bit) (twoBitsOfNat 0),
  sizeHalf := Modules.Constant.certification (.vector 2 .bit) (twoBitsOfNat 1),
  sizeByte := Modules.Constant.certification (.vector 2 .bit) (twoBitsOfNat 2),
  fetchState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  notDone := Primitives.notCertified.certification,
  waitForPrefetch := Primitives.andCertified.certification,
  notRdata := Primitives.notCertified.certification,
  byteLoad := Primitives.orCertified.certification,
  halfLoad := Primitives.orCertified.certification,
  halfOrWord := Modules.Mux.certification (.vector 2 .bit),
  loadSize := Modules.Mux.certification (.vector 2 .bit),
  capturedWordsize := Modules.Mux.certification (.vector 2 .bit),
  capturedUnsigned := Modules.BitMux.certification,
  capturedHalf := Modules.BitMux.certification,
  capturedByte := Modules.BitMux.certification,
  notPrefetch := Primitives.notCertified.certification,
  finish := Primitives.andCertified.certification,
  finishedPhase := Modules.Mux.certification (.vector 8 .bit),
  finishedDecoder := Modules.BitMux.certification,
  finishedPseudo := Modules.BitMux.certification,
  activeState := Modules.NamedTupleCombiner.certification stateMap,
  activeTransition := Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  waitState := Modules.NamedTupleCombiner.certification stateMap,
  waitTransition := Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  result := Modules.Mux.certification transitionType

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .currentFields, .updatedFields} =>
          Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .trueBit, .sizeWord, .sizeHalf, .sizeByte, .fetchState} =>
          Primitives.ConstantRule.apply,
        {.notDone, .notRdata, .notPrefetch} => Primitives.NotRule.apply,
        .waitForPrefetch => Primitives.AndRule.apply,
        {.byteLoad, .halfLoad} => Primitives.OrRule.apply,
        {.halfOrWord, .loadSize, .capturedWordsize} => Modules.Mux.Rule.select,
        {.capturedUnsigned, .capturedHalf, .capturedByte} =>
          Modules.BitMux.Rule.select,
        .finish => Primitives.AndRule.apply,
        .finishedPhase => Modules.Mux.Rule.select,
        {.finishedDecoder, .finishedPseudo} => Modules.BitMux.Rule.select,
        {.activeState, .waitState} => Modules.NamedTupleCombiner.Rule.apply,
        {.activeTransition, .waitTransition} =>
          Modules.NamedTupleCombiner.Rule.apply,
        .result => Modules.Mux.Rule.select]
  state := []

private theorem splitValue_eq_unpack (signals : SignalMap.{0})
    (value : signals.tupleType.Denote) :
    Modules.NamedTupleSplitter.splitValue signals value = signals.unpack value := by
  calc
    Modules.NamedTupleSplitter.splitValue signals value =
        Modules.NamedTupleSplitter.splitValue signals
          (signals.pack (signals.unpack value)) := by rw [signals.pack_unpack]
    _ = signals.unpack value := Modules.NamedTupleSplitter.splitValue_pack signals _

def selectedSize (inputs : Inputs) : TwoBits :=
  if inputs.instr_lb || inputs.instr_lbu then twoBitsOfNat 2
  else if inputs.instr_lh || inputs.instr_lhu then twoBitsOfNat 1
  else twoBitsOfNat 0

def waitState (updated : stateMap.Values) : stateMap.Values
  | .latched_store => true
  | field => updated field

def activeState (inputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values
  | .cpu_state => bif (!((current .mem_do_prefetch : Bool)) && inputs.mem_done)
      then stateBits cpuStateFetch else updated .cpu_state
  | .latched_store => true
  | .latched_stalu => updated .latched_stalu
  | .latched_branch => updated .latched_branch
  | .latched_is_lu => bif !(current .mem_do_rdata : Bool)
      then inputs.is_lbu_lhu_lw else updated .latched_is_lu
  | .latched_is_lh => bif !(current .mem_do_rdata : Bool)
      then inputs.instr_lh else updated .latched_is_lh
  | .latched_is_lb => bif !(current .mem_do_rdata : Bool)
      then inputs.instr_lb else updated .latched_is_lb
  | .latched_rd => updated .latched_rd
  | .mem_wordsize => bif !(current .mem_do_rdata : Bool)
      then selectedSize inputs else updated .mem_wordsize
  | .mem_do_prefetch => updated .mem_do_prefetch
  | .mem_do_rinst => updated .mem_do_rinst
  | .mem_do_rdata => updated .mem_do_rdata
  | .mem_do_wdata => updated .mem_do_wdata
  | .decoder_trigger => bif
      (!((current .mem_do_prefetch : Bool)) && inputs.mem_done)
      then true else updated .decoder_trigger
  | .decoder_pseudo_trigger => bif
      (!((current .mem_do_prefetch : Bool)) && inputs.mem_done)
      then true else updated .decoder_pseudo_trigger
  | .trap => updated .trap

def structuralTransition (inputs : Inputs) (current updated : stateMap.Values) :
    Transition :=
  if (current .mem_do_prefetch : Bool) && !inputs.mem_done then
    simpleTransition (waitState updated)
  else
    { state := activeState inputs current updated
      setRdata := !(current .mem_do_rdata : Bool) }

theorem structuralTransition_eq_loadTransition (inputs : Inputs)
    (current updated : stateMap.Values) :
    structuralTransition inputs current updated =
      loadTransition inputs current updated := by
  cases prefetch : (current .mem_do_prefetch : Bool) <;>
    cases done : inputs.mem_done <;>
    cases rdata : (current .mem_do_rdata : Bool) <;>
    cases lb : inputs.instr_lb <;> cases lbu : inputs.instr_lbu <;>
    cases lh : inputs.instr_lh <;> cases lhu : inputs.instr_lhu <;>
    simp [structuralTransition, loadTransition, prefetch, done, rdata] <;>
    congr <;> funext field <;> cases field <;>
    simp [activeState, waitState, selectedSize, SignalMap.set,
      prefetch, done, rdata, lb, lbu, lh, lhu]

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies
  let controlInputs := Inputs.unpack (hierStep.inputs .inputs)
  let current := stateMap.unpack (hierStep.inputs .current)
  let updated := stateMap.unpack (hierStep.inputs .updated)

  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      ControlInputs.signalMap.unpack (hierStep.inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      ControlInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .inputsFields =
      Modules.NamedTupleSplitter.splitValue ControlInputs.signalMap
        (hierStep.inputs .inputs) at equation
    exact equation.trans (splitValue_eq_unpack _ _)
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .currentFields =
      Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .current) at equation
    exact equation.trans ((splitValue_eq_unpack _ _).trans (by rfl))
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .updatedFields =
      Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .updated) at equation
    exact equation.trans ((splitValue_eq_unpack _ _).trans (by rfl))
  have inputField (field : ControlInputs.Field) :
      hierStep.childOutputs .inputsFields field = controlInputs.toValues field := by
    rw [inputsFieldsValue]
    cases field <;> rfl
  have memDoneValue : hierStep.childOutputs .inputsFields .mem_done =
      controlInputs.mem_done := by
    simpa [Inputs.toValues] using inputField .mem_done
  have instrLbValue : hierStep.childOutputs .inputsFields .instr_lb =
      controlInputs.instr_lb := by
    simpa [Inputs.toValues] using inputField .instr_lb
  have instrLbuValue : hierStep.childOutputs .inputsFields .instr_lbu =
      controlInputs.instr_lbu := by
    simpa [Inputs.toValues] using inputField .instr_lbu
  have instrLhValue : hierStep.childOutputs .inputsFields .instr_lh =
      controlInputs.instr_lh := by
    simpa [Inputs.toValues] using inputField .instr_lh
  have instrLhuValue : hierStep.childOutputs .inputsFields .instr_lhu =
      controlInputs.instr_lhu := by
    simpa [Inputs.toValues] using inputField .instr_lhu
  have isLoadUnsignedValue :
      hierStep.childOutputs .inputsFields .is_lbu_lhu_lw =
        controlInputs.is_lbu_lhu_lw := by
    simpa [Inputs.toValues] using inputField .is_lbu_lhu_lw

  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Primitives.ConstantRule.apply)
  have trueValue := (Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).ruleHolds Primitives.ConstantRule.apply)
  have sizeWordValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (twoBitsOfNat 0) _ _ _).mp
    ((childMatch .sizeWord).ruleHolds Primitives.ConstantRule.apply)
  have sizeHalfValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (twoBitsOfNat 1) _ _ _).mp
    ((childMatch .sizeHalf).ruleHolds Primitives.ConstantRule.apply)
  have sizeByteValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (twoBitsOfNat 2) _ _ _).mp
    ((childMatch .sizeByte).ruleHolds Primitives.ConstantRule.apply)
  have fetchStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
    ((childMatch .fetchState).ruleHolds Primitives.ConstantRule.apply)

  have notDoneValue : hierStep.childOutputs .notDone .output =
      !controlInputs.mem_done := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notDone).ruleHolds Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg Bool.not memDoneValue)
  have waitValue : hierStep.childOutputs .waitForPrefetch .output =
      ((current .mem_do_prefetch : Bool) && !controlInputs.mem_done) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .waitForPrefetch).ruleHolds Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and
      (congrFun currentFieldsValue .mem_do_prefetch) notDoneValue)
  have notRdataValue : hierStep.childOutputs .notRdata .output =
      !(current .mem_do_rdata : Bool) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notRdata).ruleHolds Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg Bool.not
      (congrFun currentFieldsValue .mem_do_rdata))

  have byteLoadValue : hierStep.childOutputs .byteLoad .output =
      (controlInputs.instr_lb || controlInputs.instr_lbu) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .byteLoad).ruleHolds Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.or instrLbValue instrLbuValue)
  have halfLoadValue : hierStep.childOutputs .halfLoad .output =
      (controlInputs.instr_lh || controlInputs.instr_lhu) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .halfLoad).ruleHolds Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.or instrLhValue instrLhuValue)
  have halfOrWordValue : hierStep.childOutputs .halfOrWord .result =
      bif (controlInputs.instr_lh || controlInputs.instr_lhu)
        then twoBitsOfNat 1 else twoBitsOfNat 0 := by
    have equation := Modules.Mux.result_of_allowed (.vector 2 .bit)
      (childMatch .halfOrWord).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr halfLoadValue sizeHalfValue sizeWordValue)
  have loadSizeValue : hierStep.childOutputs .loadSize .result =
      selectedSize controlInputs := by
    have equation := Modules.Mux.result_of_allowed (.vector 2 .bit)
      (childMatch .loadSize).allowed
    normalize_child_hyp equation unfolding wiring, context
    have result := equation.trans (bif_congr byteLoadValue
      sizeByteValue halfOrWordValue)
    cases byte : (controlInputs.instr_lb || controlInputs.instr_lbu) <;>
      cases half : (controlInputs.instr_lh || controlInputs.instr_lhu) <;>
      simp [selectedSize, byte, half] at result ⊢ <;> exact result

  have capturedWordsizeValue : hierStep.childOutputs .capturedWordsize .result =
      bif !(current .mem_do_rdata : Bool) then selectedSize controlInputs
        else updated .mem_wordsize := by
    have equation := Modules.Mux.result_of_allowed (.vector 2 .bit)
      (childMatch .capturedWordsize).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr notRdataValue loadSizeValue
      (congrFun updatedFieldsValue .mem_wordsize))

  have capturedUnsignedValue : hierStep.childOutputs .capturedUnsigned .result =
      bif !(current .mem_do_rdata : Bool) then controlInputs.is_lbu_lhu_lw
        else updated .latched_is_lu := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .capturedUnsigned).ruleHolds Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr notRdataValue isLoadUnsignedValue
      (congrFun updatedFieldsValue .latched_is_lu))
  have capturedHalfValue : hierStep.childOutputs .capturedHalf .result =
      bif !(current .mem_do_rdata : Bool) then controlInputs.instr_lh
        else updated .latched_is_lh := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .capturedHalf).ruleHolds Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr notRdataValue instrLhValue
      (congrFun updatedFieldsValue .latched_is_lh))
  have capturedByteValue : hierStep.childOutputs .capturedByte .result =
      bif !(current .mem_do_rdata : Bool) then controlInputs.instr_lb
        else updated .latched_is_lb := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .capturedByte).ruleHolds Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr notRdataValue instrLbValue
      (congrFun updatedFieldsValue .latched_is_lb))

  have notPrefetchValue : hierStep.childOutputs .notPrefetch .output =
      !(current .mem_do_prefetch : Bool) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notPrefetch).ruleHolds Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg Bool.not
      (congrFun currentFieldsValue .mem_do_prefetch))
  have finishValue : hierStep.childOutputs .finish .output =
      (!(current .mem_do_prefetch : Bool) && controlInputs.mem_done) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .finish).ruleHolds Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and
      notPrefetchValue memDoneValue)
  have finishedPhaseValue : hierStep.childOutputs .finishedPhase .result =
      bif (!(current .mem_do_prefetch : Bool) && controlInputs.mem_done)
        then stateBits cpuStateFetch else updated .cpu_state := by
    have equation := Modules.Mux.result_of_allowed (.vector 8 .bit)
      (childMatch .finishedPhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr finishValue fetchStateValue
      (congrFun updatedFieldsValue .cpu_state))
  have finishedDecoderValue : hierStep.childOutputs .finishedDecoder .result =
      bif (!(current .mem_do_prefetch : Bool) && controlInputs.mem_done)
        then true else updated .decoder_trigger := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .finishedDecoder).ruleHolds Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr finishValue trueValue
      (congrFun updatedFieldsValue .decoder_trigger))
  have finishedPseudoValue : hierStep.childOutputs .finishedPseudo .result =
      bif (!(current .mem_do_prefetch : Bool) && controlInputs.mem_done)
        then true else updated .decoder_pseudo_trigger := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .finishedPseudo).ruleHolds Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr finishValue trueValue
      (congrFun updatedFieldsValue .decoder_pseudo_trigger))

  have activeStateInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .activeState = activeState controlInputs current updated := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [activeState]
    · exact finishedPhaseValue
    · exact trueValue
    · simpa using congrFun updatedFieldsValue .latched_stalu
    · simpa using congrFun updatedFieldsValue .latched_branch
    · exact capturedUnsignedValue
    · exact capturedHalfValue
    · exact capturedByteValue
    · simpa using congrFun updatedFieldsValue .latched_rd
    · exact capturedWordsizeValue
    · simpa using congrFun updatedFieldsValue .mem_do_prefetch
    · simpa using congrFun updatedFieldsValue .mem_do_rinst
    · simpa using congrFun updatedFieldsValue .mem_do_rdata
    · simpa using congrFun updatedFieldsValue .mem_do_wdata
    · exact finishedDecoderValue
    · exact finishedPseudoValue
    · simpa using congrFun updatedFieldsValue .trap
  have activeStateValue : hierStep.childOutputs .activeState .value =
      stateMap.pack (activeState controlInputs current updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .activeState).ruleHolds Modules.NamedTupleCombiner.Rule.apply)
    rw [activeStateInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have waitStateInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .waitState = waitState updated := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [waitState]
    · simpa using congrFun updatedFieldsValue .cpu_state
    · exact trueValue
    · simpa using congrFun updatedFieldsValue .latched_stalu
    · simpa using congrFun updatedFieldsValue .latched_branch
    · simpa using congrFun updatedFieldsValue .latched_is_lu
    · simpa using congrFun updatedFieldsValue .latched_is_lh
    · simpa using congrFun updatedFieldsValue .latched_is_lb
    · simpa using congrFun updatedFieldsValue .latched_rd
    · simpa using congrFun updatedFieldsValue .mem_wordsize
    · simpa using congrFun updatedFieldsValue .mem_do_prefetch
    · simpa using congrFun updatedFieldsValue .mem_do_rinst
    · simpa using congrFun updatedFieldsValue .mem_do_rdata
    · simpa using congrFun updatedFieldsValue .mem_do_wdata
    · simpa using congrFun updatedFieldsValue .decoder_trigger
    · simpa using congrFun updatedFieldsValue .decoder_pseudo_trigger
    · simpa using congrFun updatedFieldsValue .trap
  have waitStateValue : hierStep.childOutputs .waitState .value =
      stateMap.pack (waitState updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .waitState).ruleHolds Modules.NamedTupleCombiner.Rule.apply)
    rw [waitStateInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have activeTransitionInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .activeTransition =
        ({ state := activeState controlInputs current updated
           setRdata := !(current .mem_do_rdata : Bool) } : Transition).toValues := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [Transition.toValues]
    · exact activeStateValue
    · exact falseValue
    · exact notRdataValue
    · exact falseValue
  have activeTransitionValue : hierStep.childOutputs .activeTransition .value =
      ({ state := activeState controlInputs current updated
         setRdata := !(current .mem_do_rdata : Bool) } : Transition).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .activeTransition).ruleHolds Modules.NamedTupleCombiner.Rule.apply)
    rw [activeTransitionInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have waitTransitionInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .waitTransition =
        (simpleTransition (waitState updated)).toValues := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [Transition.toValues, simpleTransition]
    · exact waitStateValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
  have waitTransitionValue : hierStep.childOutputs .waitTransition .value =
      (simpleTransition (waitState updated)).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .waitTransition).ruleHolds Modules.NamedTupleCombiner.Rule.apply)
    rw [waitTransitionInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have resultValue : hierStep.childOutputs .result .result =
      (structuralTransition controlInputs current updated).pack := by
    have equation := Modules.Mux.result_of_allowed transitionType
      (childMatch .result).allowed
    normalize_child_hyp equation unfolding wiring, context
    have equation := equation.trans (bif_congr waitValue
      waitTransitionValue activeTransitionValue)
    have packedSelection : (structuralTransition controlInputs current updated).pack =
        bif ((current .mem_do_prefetch : Bool) && !controlInputs.mem_done)
          then (simpleTransition (waitState updated)).pack
          else ({ state := activeState controlInputs current updated
                  setRdata := !(current .mem_do_rdata : Bool) } : Transition).pack := by
      cases selected : ((current .mem_do_prefetch : Bool) &&
          !controlInputs.mem_done) <;> simp [structuralTransition, selected]
    rw [packedSelection]
    exact equation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [PhaseTransition.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .transition =
        hierStep.childOutputs .result .result by exact satisfies.1 .transition]
    rw [resultValue, structuralTransition_eq_loadTransition]
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

end Silean.Examples.PicoRV.Control.LoadTransition
