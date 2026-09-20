import PicoRV.Control.ControlLoadRs2Transition
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMuxTheorems
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace PicoRV.Control.LoadRs2Transition

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Silean.Modules.Constant.certification .bit false,
  trueBit := Silean.Modules.Constant.certification .bit true,
  executeState := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateExec),
  shiftState := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateShift),
  storeState := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateStmem),
  shiftPhase := Silean.Modules.Mux.certification (.vector 8 .bit),
  shiftRinst := Silean.Modules.BitMux.certification,
  storePhase := Silean.Modules.Mux.certification (.vector 8 .bit),
  storeRinst := Silean.Modules.BitMux.certification,
  resultState := Silean.Modules.NamedTupleCombiner.certification stateMap,
  result := Silean.Modules.NamedTupleCombiner.certification TransitionValue.signalMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .updatedFields} => Silean.Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .trueBit, .executeState, .shiftState, .storeState} =>
          Silean.Primitives.ConstantRule.apply,
        .shiftPhase => Silean.Modules.Mux.Rule.select,
        .shiftRinst => Silean.Modules.BitMux.Rule.select,
        .storePhase => Silean.Modules.Mux.Rule.select,
        .storeRinst => Silean.Modules.BitMux.Rule.select,
        .resultState => Silean.Modules.NamedTupleCombiner.Rule.apply,
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

def selectedPhase (inputs : Inputs) : EightBits :=
  if inputs.is_sb_sh_sw then stateBits cpuStateStmem
  else if inputs.is_sll_srl_sra then stateBits cpuStateShift
  else stateBits cpuStateExec

def selectedRinst (inputs : Inputs) (updated : stateMap.Values) : Bool :=
  if inputs.is_sb_sh_sw then true
  else if inputs.is_sll_srl_sra then updated .mem_do_rinst
  else updated .mem_do_prefetch

def structuralState (inputs : Inputs) (updated : stateMap.Values) : stateMap.Values
  | .cpu_state => selectedPhase inputs
  | .mem_do_rinst => selectedRinst inputs updated
  | field => updated field

def structuralTransition (inputs : Inputs) (updated : stateMap.Values) : Transition :=
  simpleTransition (structuralState inputs updated)

set_option linter.unusedSimpArgs false in
theorem structuralTransition_eq_loadRs2Transition (inputs : Inputs)
    (updated : stateMap.Values) :
    structuralTransition inputs updated = loadRs2Transition inputs updated := by
  by_cases store : inputs.is_sb_sh_sw
  · simp [structuralTransition, loadRs2Transition, store, simpleTransition]
    congr
    funext field
    cases field <;> simp [structuralState, selectedPhase, selectedRinst,
      Silean.SignalMap.set, store]
  · simp [loadRs2Transition, store]
    by_cases shift : inputs.is_sll_srl_sra
    · simp [structuralTransition, shift, store, simpleTransition]
      congr
      funext field
      cases field <;> simp [structuralState, selectedPhase, selectedRinst,
        Silean.SignalMap.set, shift, store]
    · simp [structuralTransition, shift, store, simpleTransition]
      congr
      funext field
      cases field <;> simp [structuralState, selectedPhase, selectedRinst,
        Silean.SignalMap.set, shift, store]

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
  have storeSelectorValue :
      hierStep.childOutputs .inputsFields .is_sb_sh_sw =
        controlInputs.is_sb_sh_sw := by
    rw [inputsFieldsValue]
    rfl
  have shiftSelectorValue :
      hierStep.childOutputs .inputsFields .is_sll_srl_sra =
        controlInputs.is_sll_srl_sra := by
    rw [inputsFieldsValue]
    rfl

  have falseValue := Silean.Modules.Constant.output_of_allowed .bit false
    (childMatch .falseBit).allowed
  have trueValue := Silean.Modules.Constant.output_of_allowed .bit true
    (childMatch .trueBit).allowed
  have executeStateValue := Silean.Modules.Constant.output_of_allowed
    (.vector 8 .bit) (stateBits cpuStateExec)
    (childMatch .executeState).allowed
  have shiftStateValue := Silean.Modules.Constant.output_of_allowed
    (.vector 8 .bit) (stateBits cpuStateShift)
    (childMatch .shiftState).allowed
  have storeStateValue := Silean.Modules.Constant.output_of_allowed
    (.vector 8 .bit) (stateBits cpuStateStmem)
    (childMatch .storeState).allowed

  have shiftPhaseValue : hierStep.childOutputs .shiftPhase .result =
      bif controlInputs.is_sll_srl_sra then stateBits cpuStateShift
        else stateBits cpuStateExec := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 8 .bit)
      (childMatch .shiftPhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr shiftSelectorValue
      shiftStateValue executeStateValue)
  have shiftRinstValue : hierStep.childOutputs .shiftRinst .result =
      bif controlInputs.is_sll_srl_sra then updated .mem_do_rinst
        else updated .mem_do_prefetch := by
    have equation := Silean.Modules.BitMux.result_of_allowed
      (childMatch .shiftRinst).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr shiftSelectorValue
      (congrFun updatedFieldsValue .mem_do_rinst)
      (congrFun updatedFieldsValue .mem_do_prefetch))
  have storePhaseValue : hierStep.childOutputs .storePhase .result =
      bif controlInputs.is_sb_sh_sw then stateBits cpuStateStmem
        else hierStep.childOutputs .shiftPhase .result := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 8 .bit)
      (childMatch .storePhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr storeSelectorValue
      storeStateValue (Eq.refl _))
  have storeRinstValue : hierStep.childOutputs .storeRinst .result =
      bif controlInputs.is_sb_sh_sw then true
        else hierStep.childOutputs .shiftRinst .result := by
    have equation := Silean.Modules.BitMux.result_of_allowed
      (childMatch .storeRinst).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr storeSelectorValue trueValue (Eq.refl _))

  have selectedPhaseValue : hierStep.childOutputs .storePhase .result =
      selectedPhase controlInputs := by
    rw [storePhaseValue, shiftPhaseValue]
    cases store : controlInputs.is_sb_sh_sw <;>
      cases shift : controlInputs.is_sll_srl_sra <;>
      simp [selectedPhase, store, shift]
  have selectedRinstValue : hierStep.childOutputs .storeRinst .result =
      selectedRinst controlInputs updated := by
    rw [storeRinstValue, shiftRinstValue]
    cases store : controlInputs.is_sb_sh_sw <;>
      cases shift : controlInputs.is_sll_srl_sra <;>
      simp [selectedRinst, store, shift]

  have resultStateInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .resultState = structuralState controlInputs updated := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [structuralState]
    · exact selectedPhaseValue
    · simpa using congrFun updatedFieldsValue .latched_store
    · simpa using congrFun updatedFieldsValue .latched_stalu
    · simpa using congrFun updatedFieldsValue .latched_branch
    · simpa using congrFun updatedFieldsValue .latched_is_lu
    · simpa using congrFun updatedFieldsValue .latched_is_lh
    · simpa using congrFun updatedFieldsValue .latched_is_lb
    · simpa using congrFun updatedFieldsValue .latched_rd
    · simpa using congrFun updatedFieldsValue .mem_wordsize
    · simpa using congrFun updatedFieldsValue .mem_do_prefetch
    · exact selectedRinstValue
    · simpa using congrFun updatedFieldsValue .mem_do_rdata
    · simpa using congrFun updatedFieldsValue .mem_do_wdata
    · simpa using congrFun updatedFieldsValue .decoder_trigger
    · simpa using congrFun updatedFieldsValue .decoder_pseudo_trigger
    · simpa using congrFun updatedFieldsValue .trap
  have resultStateValue : hierStep.childOutputs .resultState .value =
      stateMap.pack (structuralState controlInputs updated) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .resultState).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultStateInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result =
        (structuralTransition controlInputs updated).toValues := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [structuralTransition, Transition.toValues, simpleTransition]
    · exact resultStateValue
    · exact falseValue
    · exact falseValue
    · exact falseValue
  have resultValue : hierStep.childOutputs .result .value =
      (structuralTransition controlInputs updated).pack := by
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
    rw [resultValue, structuralTransition_eq_loadRs2Transition]
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

end PicoRV.Control.LoadRs2Transition
