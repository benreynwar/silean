import PicoRV.Control.ControlExecuteTransition
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMuxTheorems
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace PicoRV.Control.ExecuteTransition

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification
    ControlInputs.signalMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Silean.Modules.Constant.certification .bit false,
  trueBit := Silean.Modules.Constant.certification .bit true,
  zeroRd := Silean.Modules.Constant.certification (.vector 5 .bit) (fiveBitsOfNat 0),
  fetchState := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  branchPhase := Silean.Modules.Mux.certification (.vector 8 .bit),
  branchDecoder := Silean.Modules.BitMux.certification,
  branchState := Silean.Modules.NamedTupleCombiner.certification stateMap,
  branchTransition := Silean.Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  ordinaryState := Silean.Modules.NamedTupleCombiner.certification stateMap,
  ordinaryTransition := Silean.Modules.NamedTupleCombiner.certification
    TransitionValue.signalMap,
  result := Silean.Modules.Mux.certification transitionType

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .updatedFields} =>
          Silean.Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .trueBit, .zeroRd, .fetchState} =>
          Silean.Primitives.ConstantRule.apply,
        .branchPhase => Silean.Modules.Mux.Rule.select,
        .branchDecoder => Silean.Modules.BitMux.Rule.select,
        {.branchState, .ordinaryState} =>
          Silean.Modules.NamedTupleCombiner.Rule.apply,
        {.branchTransition, .ordinaryTransition} =>
          Silean.Modules.NamedTupleCombiner.Rule.apply,
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
    cases field <;> simp [ordinaryState, Silean.SignalMap.set]
  · simp only [structuralTransition, branch, ↓reduceIte, executeTransition]
    cases done : inputs.mem_done <;> cases taken : inputs.alu_out_0 <;>
      congr <;> funext field <;> cases field <;>
      simp [branchState, Silean.SignalMap.set, done, taken]

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
  have zeroRdValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 5 .bit) (fiveBitsOfNat 0) _ _ _).mp
    ((childMatch .zeroRd).ruleHolds Silean.Primitives.ConstantRule.apply)
  have fetchStateValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
    ((childMatch .fetchState).ruleHolds Silean.Primitives.ConstantRule.apply)

  have branchPhaseValue : hierStep.childOutputs .branchPhase .result =
      bif controlInputs.mem_done then stateBits cpuStateFetch
        else updated .cpu_state := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 8 .bit)
      (childMatch .branchPhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr (inputField .mem_done)
      fetchStateValue (congrFun updatedFieldsValue .cpu_state))

  have branchDecoderValue : hierStep.childOutputs .branchDecoder .result =
      bif controlInputs.alu_out_0 then false else updated .decoder_trigger := by
    have equation := (Silean.Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .branchDecoder).ruleHolds Silean.Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr (inputField .alu_out_0) falseValue
      (congrFun updatedFieldsValue .decoder_trigger))

  have branchStateInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .branchState = branchState controlInputs updated := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [branchState]
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

  have branchStateValue : hierStep.childOutputs .branchState .value =
      stateMap.pack (branchState controlInputs updated) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .branchState).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [branchStateInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have ordinaryStateInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .ordinaryState = ordinaryState controlInputs updated := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [ordinaryState]
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

  have ordinaryStateValue : hierStep.childOutputs .ordinaryState .value =
      stateMap.pack (ordinaryState controlInputs updated) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .ordinaryState).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [ordinaryStateInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have branchTransitionInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .branchTransition =
        ({ state := branchState controlInputs updated
           setRinst := controlInputs.alu_out_0 } : Transition).toValues := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [Transition.toValues]
    · exact branchStateValue
    · simpa [Inputs.toValues] using inputField .alu_out_0
    · exact falseValue
    · exact falseValue

  have branchTransitionValue : hierStep.childOutputs .branchTransition .value =
      ({ state := branchState controlInputs updated
         setRinst := controlInputs.alu_out_0 } : Transition).pack := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .branchTransition).ruleHolds
        Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [branchTransitionInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have ordinaryTransitionInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .ordinaryTransition =
        ({ state := ordinaryState controlInputs updated } : Transition).toValues := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [Transition.toValues]
    · exact ordinaryStateValue
    · exact falseValue
    · exact falseValue
    · exact falseValue

  have ordinaryTransitionValue :
      hierStep.childOutputs .ordinaryTransition .value =
        ({ state := ordinaryState controlInputs updated } : Transition).pack := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .ordinaryTransition).ruleHolds
        Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [ordinaryTransitionInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have resultValue : hierStep.childOutputs .result .result =
      (structuralTransition controlInputs updated).pack := by
    have equation := Silean.Modules.Mux.result_of_allowed transitionType
      (childMatch .result).allowed
    normalize_child_hyp equation unfolding wiring, context
    have equation := equation.trans (bif_congr
      (inputField .is_beq_bne_blt_bge_bltu_bgeu)
      branchTransitionValue ordinaryTransitionValue)
    have packedSelection : (structuralTransition controlInputs updated).pack =
        bif controlInputs.is_beq_bne_blt_bge_bltu_bgeu then
          ({ state := branchState controlInputs updated
             setRinst := controlInputs.alu_out_0 } : Transition).pack
        else ({ state := ordinaryState controlInputs updated } : Transition).pack := by
      cases selected : controlInputs.is_beq_bne_blt_bge_bltu_bgeu <;>
        simp [structuralTransition, selected]
    rw [packedSelection]
    exact equation

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [PhaseTransition.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .transition =
        hierStep.childOutputs .result .result by
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
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Control.ExecuteTransition
