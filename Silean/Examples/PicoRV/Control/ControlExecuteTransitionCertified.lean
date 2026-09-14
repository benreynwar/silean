import Silean.Examples.PicoRV.Control.ControlExecuteTransition
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMuxCertified
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified

namespace Silean.Examples.PicoRV.Control.ExecuteTransition

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification
    ControlInputs.signalMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  trueBit := Modules.Constant.certification .bit true,
  zeroRd := Modules.Constant.certification (.vector 5 .bit) (fiveBitsOfNat 0),
  fetchState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  branchPhase := Modules.Mux.certification (.vector 8 .bit),
  branchDecoder := Modules.BitMux.certification,
  branchState := Modules.NamedTupleCombiner.certification stateMap,
  branchTransition := Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  ordinaryState := Modules.NamedTupleCombiner.certification stateMap,
  ordinaryTransition := Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  result := Modules.Mux.certification transitionType

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .updatedFields} =>
          Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .trueBit, .zeroRd, .fetchState} =>
          Primitives.ConstantRule.apply,
        .branchPhase => Modules.Mux.Rule.select,
        .branchDecoder => Modules.BitMux.Rule.select,
        {.branchState, .ordinaryState} =>
          Modules.NamedTupleCombiner.Rule.apply,
        {.branchTransition, .ordinaryTransition} =>
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

def branchState (inputs : Inputs) (updated : stateMap.Values) : stateMap.Values
  | .cpu_state => bif inputs.mem_done then stateBits cpuStateFetch
      else updated .cpu_state
  | .latched_store => inputs.alu_out_0
  | .latched_stalu => updated .latched_stalu
  | .latched_branch => inputs.alu_out_0
  | .latched_is_lu => updated .latched_is_lu
  | .latched_is_lh => updated .latched_is_lh
  | .latched_is_lb => updated .latched_is_lb
  | .latched_rd => fiveBitsOfNat 0
  | .mem_wordsize => updated .mem_wordsize
  | .mem_do_prefetch => updated .mem_do_prefetch
  | .mem_do_rinst => updated .mem_do_rinst
  | .mem_do_rdata => updated .mem_do_rdata
  | .mem_do_wdata => updated .mem_do_wdata
  | .decoder_trigger => bif inputs.alu_out_0 then false
      else updated .decoder_trigger
  | .decoder_pseudo_trigger => updated .decoder_pseudo_trigger
  | .trap => updated .trap

def ordinaryState (inputs : Inputs) (updated : stateMap.Values) : stateMap.Values
  | .cpu_state => stateBits cpuStateFetch
  | .latched_store => true
  | .latched_stalu => true
  | .latched_branch => inputs.instr_jalr
  | .latched_is_lu => updated .latched_is_lu
  | .latched_is_lh => updated .latched_is_lh
  | .latched_is_lb => updated .latched_is_lb
  | .latched_rd => updated .latched_rd
  | .mem_wordsize => updated .mem_wordsize
  | .mem_do_prefetch => updated .mem_do_prefetch
  | .mem_do_rinst => updated .mem_do_rinst
  | .mem_do_rdata => updated .mem_do_rdata
  | .mem_do_wdata => updated .mem_do_wdata
  | .decoder_trigger => updated .decoder_trigger
  | .decoder_pseudo_trigger => updated .decoder_pseudo_trigger
  | .trap => updated .trap

def structuralTransition (inputs : Inputs)
    (updated : stateMap.Values) : Transition :=
  if inputs.is_beq_bne_blt_bge_bltu_bgeu then
    { state := branchState inputs updated, setRinst := inputs.alu_out_0 }
  else
    { state := ordinaryState inputs updated }

theorem structuralTransition_eq_executeTransition (inputs : Inputs)
    (updated : stateMap.Values) :
    structuralTransition inputs updated = executeTransition inputs updated := by
  cases branch : inputs.is_beq_bne_blt_bge_bltu_bgeu
  · simp only [structuralTransition, branch, Bool.false_eq_true, ↓reduceIte,
      executeTransition]
    congr
    funext field
    cases field <;> simp [ordinaryState, SignalMap.set]
  · simp only [structuralTransition, branch, ↓reduceIte, executeTransition]
    cases done : inputs.mem_done <;> cases taken : inputs.alu_out_0 <;>
      congr <;> funext field <;> cases field <;>
      simp [branchState, SignalMap.set, done, taken]

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

  have inputField (field : ControlInputs.Field) :
      (proposal.2 .inputsFields).outputs field = controlInputs.toValues field := by
    rw [inputsFieldsValue]
    cases field <;> rfl

  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have trueValue := (Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).1.1 Primitives.ConstantRule.apply)
  have zeroRdValue := (Modules.Constant.outputRule_holds_iff
    (.vector 5 .bit) (fiveBitsOfNat 0) _ _ _).mp
    ((childMatch .zeroRd).1.1 Primitives.ConstantRule.apply)
  have fetchStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
    ((childMatch .fetchState).1.1 Primitives.ConstantRule.apply)

  have branchPhaseValue : (proposal.2 .branchPhase).outputs .result =
      bif controlInputs.mem_done then stateBits cpuStateFetch
        else updated .cpu_state := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .branchPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .mem_done, updatedFieldsValue, fetchStateValue] at equation
    exact equation

  have branchDecoderValue : (proposal.2 .branchDecoder).outputs .result =
      bif controlInputs.alu_out_0 then false else updated .decoder_trigger := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .branchDecoder).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .alu_out_0, updatedFieldsValue, falseValue] at equation
    exact equation

  have branchStateInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .branchState = branchState controlInputs updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, branchState]
    · exact branchPhaseValue
    · simpa [Inputs.toValues] using inputField .alu_out_0
    · simpa using congrFun updatedFieldsValue .latched_stalu
    · simpa [Inputs.toValues] using inputField .alu_out_0
    · simpa using congrFun updatedFieldsValue .latched_is_lu
    · simpa using congrFun updatedFieldsValue .latched_is_lh
    · simpa using congrFun updatedFieldsValue .latched_is_lb
    · exact zeroRdValue
    · simpa using congrFun updatedFieldsValue .mem_wordsize
    · simpa using congrFun updatedFieldsValue .mem_do_prefetch
    · simpa using congrFun updatedFieldsValue .mem_do_rinst
    · simpa using congrFun updatedFieldsValue .mem_do_rdata
    · simpa using congrFun updatedFieldsValue .mem_do_wdata
    · exact branchDecoderValue
    · simpa using congrFun updatedFieldsValue .decoder_pseudo_trigger
    · simpa using congrFun updatedFieldsValue .trap

  have branchStateValue : (proposal.2 .branchState).outputs .value =
      stateMap.pack (branchState controlInputs updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .branchState).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [branchStateInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have ordinaryStateInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .ordinaryState = ordinaryState controlInputs updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, ordinaryState]
    · exact fetchStateValue
    · exact trueValue
    · exact trueValue
    · simpa [Inputs.toValues] using inputField .instr_jalr
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

  have ordinaryStateValue : (proposal.2 .ordinaryState).outputs .value =
      stateMap.pack (ordinaryState controlInputs updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .ordinaryState).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [ordinaryStateInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have branchTransitionInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .branchTransition =
        ({ state := branchState controlInputs updated
           setRinst := controlInputs.alu_out_0 } : Transition).toValues := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, Transition.toValues]
    · exact branchStateValue
    · simpa [Inputs.toValues] using inputField .alu_out_0
    · exact falseValue
    · exact falseValue

  have branchTransitionValue : (proposal.2 .branchTransition).outputs .value =
      ({ state := branchState controlInputs updated
         setRinst := controlInputs.alu_out_0 } : Transition).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .branchTransition).1.1
        Modules.NamedTupleCombiner.Rule.apply)
    rw [branchTransitionInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have ordinaryTransitionInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .ordinaryTransition =
        ({ state := ordinaryState controlInputs updated } : Transition).toValues := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, Transition.toValues]
    · exact ordinaryStateValue
    · exact falseValue
    · exact falseValue
    · exact falseValue

  have ordinaryTransitionValue :
      (proposal.2 .ordinaryTransition).outputs .value =
        ({ state := ordinaryState controlInputs updated } : Transition).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .ordinaryTransition).1.1
        Modules.NamedTupleCombiner.Rule.apply)
    rw [ordinaryTransitionInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have resultValue : (proposal.2 .result).outputs .result =
      (structuralTransition controlInputs updated).pack := by
    have equation := Modules.Mux.result_of_evaluatesTo transitionType
      _ _ _ _ (childMatch .result).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .is_beq_bne_blt_bge_bltu_bgeu,
      ordinaryTransitionValue, branchTransitionValue] at equation
    simp only [Inputs.toValues] at equation
    have packedSelection : (structuralTransition controlInputs updated).pack =
        bif controlInputs.is_beq_bne_blt_bge_bltu_bgeu then
          ({ state := branchState controlInputs updated
             setRinst := controlInputs.alu_out_0 } : Transition).pack
        else ({ state := ordinaryState controlInputs updated } : Transition).pack := by
      cases selected : controlInputs.is_beq_bne_blt_bge_bltu_bgeu <;>
        simp [structuralTransition, selected]
    rw [packedSelection]
    exact equation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [PhaseTransition.outputRule_holds_iff]
    rw [show proposal.outputs .transition =
        (proposal.2 .result).outputs .result by
      exact satisfies.1 .transition]
    rw [resultValue, structuralTransition_eq_executeTransition]
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

end Silean.Examples.PicoRV.Control.ExecuteTransition
