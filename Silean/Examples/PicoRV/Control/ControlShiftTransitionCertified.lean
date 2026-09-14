import Silean.Examples.PicoRV.Control.ControlShiftTransition
import Silean.Examples.PicoRV.Control.ControlBitLaws
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMuxCertified
import Silean.Modules.EqualsConstant.EqualsConstantCertified
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified

namespace Silean.Examples.PicoRV.Control.ShiftTransition

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  trueBit := Modules.Constant.certification .bit true,
  fetchState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  shiftIsZero := Modules.EqualsConstant.certification (.vector 5 .bit)
    (fiveBitsOfNat 0),
  selectedPhase := Modules.Mux.certification (.vector 8 .bit),
  selectedRinst := Modules.BitMux.certification,
  resultState := Modules.NamedTupleCombiner.certification stateMap,
  result := Modules.NamedTupleCombiner.certification TransitionValue.signalMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .updatedFields} => Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .trueBit, .fetchState} => Primitives.ConstantRule.apply,
        .shiftIsZero => Modules.EqualsConstant.Rule.apply,
        .selectedPhase => Modules.Mux.Rule.select,
        .selectedRinst => Modules.BitMux.Rule.select,
        .resultState => Modules.NamedTupleCombiner.Rule.apply,
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

private theorem equalFiveZero (bits : Fin 5 → Bool) :
    (SignalType.vector 5 .bit).equal bits (fiveBitsOfNat 0) =
      decide (BitVector.toNat 5 bits = 0) := by
  have representation : fiveBitsOfNat 0 = BitVector.ofNat 5 0 := by
    funext index
    simp [fiveBitsOfNat, BitVector.ofNat]
  rw [representation]
  exact signalTypeEqual_ofNat 5 0 bits (by decide)

def selectedPhaseValue (inputs : Inputs) (updated : stateMap.Values) : EightBits :=
  if shiftAmount inputs = 0 then stateBits cpuStateFetch else updated .cpu_state

def selectedRinstValue (inputs : Inputs) (updated : stateMap.Values) : Bool :=
  if shiftAmount inputs = 0 then updated .mem_do_prefetch
  else updated .mem_do_rinst

def structuralState (inputs : Inputs) (updated : stateMap.Values) : stateMap.Values
  | .cpu_state => selectedPhaseValue inputs updated
  | .latched_store => true
  | .mem_do_rinst => selectedRinstValue inputs updated
  | field => updated field

def structuralTransition (inputs : Inputs) (updated : stateMap.Values) : Transition :=
  simpleTransition (structuralState inputs updated)

theorem structuralTransition_eq_shiftTransition (inputs : Inputs)
    (updated : stateMap.Values) :
    structuralTransition inputs updated = shiftTransition inputs updated := by
  by_cases zero : shiftAmount inputs = 0
  · simp [structuralTransition, shiftTransition, zero, simpleTransition]
    congr
    funext field
    cases field <;> simp [structuralState, selectedPhaseValue,
      selectedRinstValue, SignalMap.set, zero]
  · simp [structuralTransition, shiftTransition, zero, simpleTransition]
    congr
    funext field
    cases field <;> simp [structuralState, selectedPhaseValue,
      selectedRinstValue, SignalMap.set, zero]

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralStateValue proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralStateValue, proposal, satisfies

  let controlInputs := Inputs.unpack (inputs .inputs)
  let updated := stateMap.unpack (inputs .updated)

  have inputsFieldsValue : (proposal.2 .inputsFields).outputs =
      ControlInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      ControlInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [splitValue_eq_unpack] using equation
  have updatedFieldsValue : (proposal.2 .updatedFields).outputs = updated := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [splitValue_eq_unpack, updated] using equation
  have regShiftValue : (proposal.2 .inputsFields).outputs .reg_sh =
      controlInputs.reg_sh := by
    rw [inputsFieldsValue]
    rfl

  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have trueValue := (Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).1.1 Primitives.ConstantRule.apply)
  have fetchValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
    ((childMatch .fetchState).1.1 Primitives.ConstantRule.apply)
  have shiftZeroValue : (proposal.2 .shiftIsZero).outputs .result =
      decide (shiftAmount controlInputs = 0) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 5 .bit) (fiveBitsOfNat 0) _ _ _).mp
      ((childMatch .shiftIsZero).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [regShiftValue, equalFiveZero] at equation
    change (proposal.2 .shiftIsZero).outputs .result =
      decide (BitVector.toNat 5 controlInputs.reg_sh = 0) at equation
    exact equation
  have phaseValue : (proposal.2 .selectedPhase).outputs .result =
      selectedPhaseValue controlInputs updated := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .selectedPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [shiftZeroValue, updatedFieldsValue, fetchValue] at equation
    by_cases zero : shiftAmount controlInputs = 0 <;>
      simp [selectedPhaseValue, zero] at equation ⊢ <;> exact equation
  have rinstValue : (proposal.2 .selectedRinst).outputs .result =
      selectedRinstValue controlInputs updated := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .selectedRinst).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [shiftZeroValue, updatedFieldsValue] at equation
    by_cases zero : shiftAmount controlInputs = 0 <;>
      simp [selectedRinstValue, zero] at equation ⊢ <;> exact equation

  have resultStateInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .resultState = structuralState controlInputs updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, structuralState]
    · exact phaseValue
    · exact trueValue
    · simpa using congrFun updatedFieldsValue .latched_stalu
    · simpa using congrFun updatedFieldsValue .latched_branch
    · simpa using congrFun updatedFieldsValue .latched_is_lu
    · simpa using congrFun updatedFieldsValue .latched_is_lh
    · simpa using congrFun updatedFieldsValue .latched_is_lb
    · simpa using congrFun updatedFieldsValue .latched_rd
    · simpa using congrFun updatedFieldsValue .mem_wordsize
    · simpa using congrFun updatedFieldsValue .mem_do_prefetch
    · exact rinstValue
    · simpa using congrFun updatedFieldsValue .mem_do_rdata
    · simpa using congrFun updatedFieldsValue .mem_do_wdata
    · simpa using congrFun updatedFieldsValue .decoder_trigger
    · simpa using congrFun updatedFieldsValue .decoder_pseudo_trigger
    · simpa using congrFun updatedFieldsValue .trap
  have resultStateValue : (proposal.2 .resultState).outputs .value =
      stateMap.pack (structuralState controlInputs updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .resultState).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resultStateInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result =
        (structuralTransition controlInputs updated).toValues := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value,
        structuralTransition, Transition.toValues, simpleTransition]
    · exact resultStateValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
  have resultValue : (proposal.2 .result).outputs .value =
      (structuralTransition controlInputs updated).pack := by
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
    rw [resultValue, structuralTransition_eq_shiftTransition]
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

end Silean.Examples.PicoRV.Control.ShiftTransition
