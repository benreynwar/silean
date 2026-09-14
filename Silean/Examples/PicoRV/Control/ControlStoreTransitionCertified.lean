import Silean.Examples.PicoRV.Control.ControlStoreTransition
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMuxCertified
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
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
  have instrShValue : (proposal.2 .inputsFields).outputs .instr_sh =
      controlInputs.instr_sh := by
    simpa [Inputs.toValues] using inputField .instr_sh
  have instrSbValue : (proposal.2 .inputsFields).outputs .instr_sb =
      controlInputs.instr_sb := by
    simpa [Inputs.toValues] using inputField .instr_sb

  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have trueValue := (Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).1.1 Primitives.ConstantRule.apply)
  have sizeWordValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (twoBitsOfNat 0) _ _ _).mp
    ((childMatch .sizeWord).1.1 Primitives.ConstantRule.apply)
  have sizeHalfValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (twoBitsOfNat 1) _ _ _).mp
    ((childMatch .sizeHalf).1.1 Primitives.ConstantRule.apply)
  have sizeByteValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (twoBitsOfNat 2) _ _ _).mp
    ((childMatch .sizeByte).1.1 Primitives.ConstantRule.apply)
  have fetchStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
    ((childMatch .fetchState).1.1 Primitives.ConstantRule.apply)

  have notDoneValue : (proposal.2 .notDone).outputs .output =
      !controlInputs.mem_done := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notDone).1.1 Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .mem_done] at equation
    simpa [Inputs.toValues] using equation
  have waitValue : (proposal.2 .waitForPrefetch).outputs .output =
      ((current .mem_do_prefetch : Bool) && !controlInputs.mem_done) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .waitForPrefetch).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, notDoneValue] at equation
    exact equation
  have notWdataValue : (proposal.2 .notWdata).outputs .output =
      !(current .mem_do_wdata : Bool) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notWdata).1.1 Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue] at equation
    exact equation

  have halfOrWordValue : (proposal.2 .halfOrWord).outputs .result =
      bif controlInputs.instr_sh then twoBitsOfNat 1 else twoBitsOfNat 0 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 2 .bit)
      _ _ _ _ (childMatch .halfOrWord).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [instrShValue, sizeWordValue, sizeHalfValue] at equation
    exact equation
  have storeSizeValue : (proposal.2 .storeSize).outputs .result =
      selectedSize controlInputs := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 2 .bit)
      _ _ _ _ (childMatch .storeSize).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [instrSbValue, halfOrWordValue, sizeByteValue] at equation
    cases byte : controlInputs.instr_sb <;>
      cases half : controlInputs.instr_sh <;>
      simp [selectedSize, byte, half] at equation ⊢ <;>
      exact equation
  have startedWordsizeValue : (proposal.2 .startedWordsize).outputs .result =
      bif !(current .mem_do_wdata : Bool) then selectedSize controlInputs
        else updated .mem_wordsize := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 2 .bit)
      _ _ _ _ (childMatch .startedWordsize).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [notWdataValue, updatedFieldsValue, storeSizeValue] at equation
    exact equation

  have notPrefetchValue : (proposal.2 .notPrefetch).outputs .output =
      !(current .mem_do_prefetch : Bool) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notPrefetch).1.1 Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue] at equation
    exact equation
  have finishValue : (proposal.2 .finish).outputs .output =
      (!(current .mem_do_prefetch : Bool) && controlInputs.mem_done) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .finish).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [notPrefetchValue, inputField .mem_done] at equation
    simpa [Inputs.toValues] using equation
  have finishedPhaseValue : (proposal.2 .finishedPhase).outputs .result =
      bif (!(current .mem_do_prefetch : Bool) && controlInputs.mem_done)
        then stateBits cpuStateFetch else updated .cpu_state := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .finishedPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [finishValue, updatedFieldsValue, fetchStateValue] at equation
    exact equation
  have finishedDecoderValue : (proposal.2 .finishedDecoder).outputs .result =
      bif (!(current .mem_do_prefetch : Bool) && controlInputs.mem_done)
        then true else updated .decoder_trigger := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .finishedDecoder).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [finishValue, updatedFieldsValue, trueValue] at equation
    exact equation
  have finishedPseudoValue : (proposal.2 .finishedPseudo).outputs .result =
      bif (!(current .mem_do_prefetch : Bool) && controlInputs.mem_done)
        then true else updated .decoder_pseudo_trigger := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .finishedPseudo).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [finishValue, updatedFieldsValue, trueValue] at equation
    exact equation

  have activeStateInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .activeState = activeState controlInputs current updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, activeState]
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
  have activeStateValue : (proposal.2 .activeState).outputs .value =
      stateMap.pack (activeState controlInputs current updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .activeState).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [activeStateInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have activeTransitionInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .activeTransition =
        ({ state := activeState controlInputs current updated
           setWdata := !(current .mem_do_wdata : Bool) } : Transition).toValues := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, Transition.toValues]
    · exact activeStateValue
    · exact falseValue
    · exact falseValue
    · exact notWdataValue
  have activeTransitionValue : (proposal.2 .activeTransition).outputs .value =
      ({ state := activeState controlInputs current updated
         setWdata := !(current .mem_do_wdata : Bool) } : Transition).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .activeTransition).1.1
        Modules.NamedTupleCombiner.Rule.apply)
    rw [activeTransitionInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have waitTransitionInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .waitTransition = (simpleTransition updated).toValues := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value, Transition.toValues, simpleTransition]
    · exact stateMap.pack_unpack (inputs .updated)
    · exact falseValue
    · exact falseValue
    · exact falseValue
  have waitTransitionValue : (proposal.2 .waitTransition).outputs .value =
      (simpleTransition updated).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .waitTransition).1.1
        Modules.NamedTupleCombiner.Rule.apply)
    rw [waitTransitionInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have resultValue : (proposal.2 .result).outputs .result =
      (structuralTransition controlInputs current updated).pack := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .result).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [waitValue, activeTransitionValue, waitTransitionValue] at equation
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
    rw [show proposal.outputs .transition =
        (proposal.2 .result).outputs .result by exact satisfies.1 .transition]
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

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Control.StoreTransition
