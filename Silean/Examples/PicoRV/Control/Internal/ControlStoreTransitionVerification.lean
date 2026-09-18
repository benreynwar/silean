import Silean.Examples.PicoRV.Control.ControlStoreTransition
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

namespace Silean.Examples.PicoRV.Control.StoreTransition

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification
    ControlInputs.signalMap,
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
  notWdata := Primitives.notCertified.certification,
  halfOrWord := Modules.Mux.certification (.vector 2 .bit),
  storeSize := Modules.Mux.certification (.vector 2 .bit),
  startedWordsize := Modules.Mux.certification (.vector 2 .bit),
  notPrefetch := Primitives.notCertified.certification,
  finish := Primitives.andCertified.certification,
  finishedPhase := Modules.Mux.certification (.vector 8 .bit),
  finishedDecoder := Modules.BitMux.certification,
  finishedPseudo := Modules.BitMux.certification,
  activeState := Modules.NamedTupleCombiner.certification stateMap,
  activeTransition := Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
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
        {.notDone, .notWdata, .notPrefetch} => Primitives.NotRule.apply,
        .waitForPrefetch => Primitives.AndRule.apply,
        {.halfOrWord, .storeSize, .startedWordsize} => Modules.Mux.Rule.select,
        .finish => Primitives.AndRule.apply,
        .finishedPhase => Modules.Mux.Rule.select,
        {.finishedDecoder, .finishedPseudo} => Modules.BitMux.Rule.select,
        .activeState => Modules.NamedTupleCombiner.Rule.apply,
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
    _ = signals.unpack value :=
      Modules.NamedTupleSplitter.splitValue_pack signals _

def selectedSize (inputs : Inputs) : TwoBits :=
  if inputs.instr_sb then twoBitsOfNat 2
  else if inputs.instr_sh then twoBitsOfNat 1 else twoBitsOfNat 0

def activeState (inputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values
  | .cpu_state => bif (!((current .mem_do_prefetch : Bool)) && inputs.mem_done)
      then stateBits cpuStateFetch else updated .cpu_state
  | .latched_store => updated .latched_store
  | .latched_stalu => updated .latched_stalu
  | .latched_branch => updated .latched_branch
  | .latched_is_lu => updated .latched_is_lu
  | .latched_is_lh => updated .latched_is_lh
  | .latched_is_lb => updated .latched_is_lb
  | .latched_rd => updated .latched_rd
  | .mem_wordsize => bif !(current .mem_do_wdata : Bool)
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
    simpleTransition updated
  else
    { state := activeState inputs current updated
      setWdata := !(current .mem_do_wdata : Bool) }

theorem structuralTransition_eq_storeTransition (inputs : Inputs)
    (current updated : stateMap.Values) :
    structuralTransition inputs current updated =
      storeTransition inputs current updated := by
  cases prefetch : (current .mem_do_prefetch : Bool) <;>
    cases done : inputs.mem_done <;>
    cases wdata : (current .mem_do_wdata : Bool) <;>
    cases byte : inputs.instr_sb <;> cases half : inputs.instr_sh <;>
    simp [structuralTransition, storeTransition,
      prefetch, done, wdata, byte, half] <;>
    congr <;> funext field <;> cases field <;>
    simp [activeState, selectedSize, SignalMap.set,
      prefetch, done, wdata, byte, half]

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
  have instrShValue : hierStep.childOutputs .inputsFields .instr_sh =
      controlInputs.instr_sh := by
    simpa [Inputs.toValues] using inputField .instr_sh
  have instrSbValue : hierStep.childOutputs .inputsFields .instr_sb =
      controlInputs.instr_sb := by
    simpa [Inputs.toValues] using inputField .instr_sb

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
    exact equation.trans (congrArg Bool.not (inputField .mem_done))
  have waitValue : hierStep.childOutputs .waitForPrefetch .output =
      ((current .mem_do_prefetch : Bool) && !controlInputs.mem_done) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .waitForPrefetch).ruleHolds Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and
      (congrFun currentFieldsValue .mem_do_prefetch) notDoneValue)
  have notWdataValue : hierStep.childOutputs .notWdata .output =
      !(current .mem_do_wdata : Bool) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notWdata).ruleHolds Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg Bool.not
      (congrFun currentFieldsValue .mem_do_wdata))

  have halfOrWordValue : hierStep.childOutputs .halfOrWord .result =
      bif controlInputs.instr_sh then twoBitsOfNat 1 else twoBitsOfNat 0 := by
    have equation := Modules.Mux.result_of_allowed (.vector 2 .bit)
      (childMatch .halfOrWord).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr instrShValue
      sizeHalfValue sizeWordValue)
  have storeSizeValue : hierStep.childOutputs .storeSize .result =
      selectedSize controlInputs := by
    have equation := Modules.Mux.result_of_allowed (.vector 2 .bit)
      (childMatch .storeSize).allowed
    normalize_child_hyp equation unfolding wiring, context
    have result := equation.trans (bif_congr instrSbValue
      sizeByteValue halfOrWordValue)
    cases byte : controlInputs.instr_sb <;>
      cases half : controlInputs.instr_sh <;>
      simp [selectedSize, byte, half] at result ⊢ <;>
      exact result
  have startedWordsizeValue : hierStep.childOutputs .startedWordsize .result =
      bif !(current .mem_do_wdata : Bool) then selectedSize controlInputs
        else updated .mem_wordsize := by
    have equation := Modules.Mux.result_of_allowed (.vector 2 .bit)
      (childMatch .startedWordsize).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr notWdataValue storeSizeValue
      (congrFun updatedFieldsValue .mem_wordsize))

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
    exact equation.trans (apply₂_congr Bool.and notPrefetchValue
      (inputField .mem_done))
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
    · simpa using congrFun updatedFieldsValue .latched_store
    · simpa using congrFun updatedFieldsValue .latched_stalu
    · simpa using congrFun updatedFieldsValue .latched_branch
    · simpa using congrFun updatedFieldsValue .latched_is_lu
    · simpa using congrFun updatedFieldsValue .latched_is_lh
    · simpa using congrFun updatedFieldsValue .latched_is_lb
    · simpa using congrFun updatedFieldsValue .latched_rd
    · exact startedWordsizeValue
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

  have activeTransitionInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .activeTransition =
        ({ state := activeState controlInputs current updated
           setWdata := !(current .mem_do_wdata : Bool) } : Transition).toValues := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [Transition.toValues]
    · exact activeStateValue
    · exact falseValue
    · exact falseValue
    · exact notWdataValue
  have activeTransitionValue : hierStep.childOutputs .activeTransition .value =
      ({ state := activeState controlInputs current updated
         setWdata := !(current .mem_do_wdata : Bool) } : Transition).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .activeTransition).ruleHolds
        Modules.NamedTupleCombiner.Rule.apply)
    rw [activeTransitionInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have waitTransitionInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .waitTransition = (simpleTransition updated).toValues := by
    funext field
    cases field <;>
      simp only [body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        Transition.toValues, simpleTransition]
    · exact stateMap.pack_unpack (hierStep.inputs .updated)
    · exact falseValue
    · exact falseValue
    · exact falseValue
  have waitTransitionValue : hierStep.childOutputs .waitTransition .value =
      (simpleTransition updated).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .waitTransition).ruleHolds
        Modules.NamedTupleCombiner.Rule.apply)
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
          then (simpleTransition updated).pack
          else ({ state := activeState controlInputs current updated
                  setWdata := !(current .mem_do_wdata : Bool) } : Transition).pack := by
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
    rw [resultValue, structuralTransition_eq_storeTransition]
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

end Silean.Examples.PicoRV.Control.StoreTransition
