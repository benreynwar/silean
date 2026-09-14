import Silean.Examples.PicoRV.Control.ControlLoadRs2Transition
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMuxCertified
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified

namespace Silean.Examples.PicoRV.Control.LoadRs2Transition

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  trueBit := Modules.Constant.certification .bit true,
  executeState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateExec),
  shiftState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateShift),
  storeState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateStmem),
  shiftPhase := Modules.Mux.certification (.vector 8 .bit),
  shiftRinst := Modules.BitMux.certification,
  storePhase := Modules.Mux.certification (.vector 8 .bit),
  storeRinst := Modules.BitMux.certification,
  resultState := Modules.NamedTupleCombiner.certification stateMap,
  result := Modules.NamedTupleCombiner.certification TransitionValue.signalMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .updatedFields} => Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .trueBit, .executeState, .shiftState, .storeState} =>
          Primitives.ConstantRule.apply,
        .shiftPhase => Modules.Mux.Rule.select,
        .shiftRinst => Modules.BitMux.Rule.select,
        .storePhase => Modules.Mux.Rule.select,
        .storeRinst => Modules.BitMux.Rule.select,
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
      SignalMap.set, store]
  · simp [loadRs2Transition, store]
    by_cases shift : inputs.is_sll_srl_sra
    · simp [structuralTransition, shift, store, simpleTransition]
      congr
      funext field
      cases field <;> simp [structuralState, selectedPhase, selectedRinst,
        SignalMap.set, shift, store]
    · simp [structuralTransition, shift, store, simpleTransition]
      congr
      funext field
      cases field <;> simp [structuralState, selectedPhase, selectedRinst,
        SignalMap.set, shift, store]

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
  have storeSelectorValue :
      (proposal.2 .inputsFields).outputs .is_sb_sh_sw =
        controlInputs.is_sb_sh_sw := by
    rw [inputsFieldsValue]
    rfl
  have shiftSelectorValue :
      (proposal.2 .inputsFields).outputs .is_sll_srl_sra =
        controlInputs.is_sll_srl_sra := by
    rw [inputsFieldsValue]
    rfl

  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have trueValue := (Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).1.1 Primitives.ConstantRule.apply)
  have executeStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateExec) _ _ _).mp
    ((childMatch .executeState).1.1 Primitives.ConstantRule.apply)
  have shiftStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateShift) _ _ _).mp
    ((childMatch .shiftState).1.1 Primitives.ConstantRule.apply)
  have storeStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateStmem) _ _ _).mp
    ((childMatch .storeState).1.1 Primitives.ConstantRule.apply)

  have shiftPhaseValue : (proposal.2 .shiftPhase).outputs .result =
      bif controlInputs.is_sll_srl_sra then stateBits cpuStateShift
        else stateBits cpuStateExec := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .shiftPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [shiftSelectorValue, executeStateValue, shiftStateValue] at equation
    exact equation
  have shiftRinstValue : (proposal.2 .shiftRinst).outputs .result =
      bif controlInputs.is_sll_srl_sra then updated .mem_do_rinst
        else updated .mem_do_prefetch := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .shiftRinst).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [shiftSelectorValue, updatedFieldsValue] at equation
    exact equation
  have storePhaseValue : (proposal.2 .storePhase).outputs .result =
      bif controlInputs.is_sb_sh_sw then stateBits cpuStateStmem
        else (proposal.2 .shiftPhase).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .storePhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storeSelectorValue, storeStateValue] at equation
    exact equation
  have storeRinstValue : (proposal.2 .storeRinst).outputs .result =
      bif controlInputs.is_sb_sh_sw then true
        else (proposal.2 .shiftRinst).outputs .result := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .storeRinst).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storeSelectorValue, trueValue] at equation
    exact equation

  have selectedPhaseValue : (proposal.2 .storePhase).outputs .result =
      selectedPhase controlInputs := by
    rw [storePhaseValue, shiftPhaseValue]
    cases store : controlInputs.is_sb_sh_sw <;>
      cases shift : controlInputs.is_sll_srl_sra <;>
      simp [selectedPhase, store, shift]
  have selectedRinstValue : (proposal.2 .storeRinst).outputs .result =
      selectedRinst controlInputs updated := by
    rw [storeRinstValue, shiftRinstValue]
    cases store : controlInputs.is_sb_sh_sw <;>
      cases shift : controlInputs.is_sll_srl_sra <;>
      simp [selectedRinst, store, shift]

  have resultStateInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .resultState = structuralState controlInputs updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, structuralState]
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Control.LoadRs2Transition
