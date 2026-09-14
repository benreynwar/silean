import Silean.Examples.PicoRV.Control.ControlLoadRs1Transition
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMuxCertified
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified

namespace Silean.Examples.PicoRV.Control.LoadRs1Transition

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  trueBit := Modules.Constant.certification .bit true,
  trapState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateTrap),
  executeState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateExec),
  loadState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateLdmem),
  shiftState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateShift),
  storeState := Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateStmem),
  regShiftPhase := Modules.Mux.certification (.vector 8 .bit),
  regShiftRinst := Modules.BitMux.certification,
  storePhase := Modules.Mux.certification (.vector 8 .bit),
  storeRinst := Modules.BitMux.certification,
  immediateAluPhase := Modules.Mux.certification (.vector 8 .bit),
  immediateAluRinst := Modules.BitMux.certification,
  immediateShiftPhase := Modules.Mux.certification (.vector 8 .bit),
  immediateShiftRinst := Modules.BitMux.certification,
  loadPhase := Modules.Mux.certification (.vector 8 .bit),
  loadRinst := Modules.BitMux.certification,
  directPhase := Modules.Mux.certification (.vector 8 .bit),
  directRinst := Modules.BitMux.certification,
  trapPhase := Modules.Mux.certification (.vector 8 .bit),
  trapRinst := Modules.BitMux.certification,
  resultState := Modules.NamedTupleCombiner.certification stateMap,
  result := Modules.NamedTupleCombiner.certification TransitionValue.signalMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .updatedFields} => Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .trueBit, .trapState, .executeState, .loadState,
          .shiftState, .storeState} => Primitives.ConstantRule.apply,
        .regShiftPhase => Modules.Mux.Rule.select,
        .regShiftRinst => Modules.BitMux.Rule.select,
        .storePhase => Modules.Mux.Rule.select,
        .storeRinst => Modules.BitMux.Rule.select,
        .immediateAluPhase => Modules.Mux.Rule.select,
        .immediateAluRinst => Modules.BitMux.Rule.select,
        .immediateShiftPhase => Modules.Mux.Rule.select,
        .immediateShiftRinst => Modules.BitMux.Rule.select,
        .loadPhase => Modules.Mux.Rule.select,
        .loadRinst => Modules.BitMux.Rule.select,
        .directPhase => Modules.Mux.Rule.select,
        .directRinst => Modules.BitMux.Rule.select,
        .trapPhase => Modules.Mux.Rule.select,
        .trapRinst => Modules.BitMux.Rule.select,
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
  if inputs.instr_trap then stateBits cpuStateTrap
  else if inputs.is_lui_auipc_jal then stateBits cpuStateExec
  else if inputs.is_lb_lh_lw_lbu_lhu then stateBits cpuStateLdmem
  else if inputs.is_slli_srli_srai then stateBits cpuStateShift
  else if inputs.is_jalr_addi_slti_sltiu_xori_ori_andi then stateBits cpuStateExec
  else if inputs.is_sb_sh_sw then stateBits cpuStateStmem
  else if inputs.is_sll_srl_sra then stateBits cpuStateShift
  else stateBits cpuStateExec

def selectedRinst (inputs : Inputs) (updated : stateMap.Values) : Bool :=
  if inputs.instr_trap then updated .mem_do_rinst
  else if inputs.is_lui_auipc_jal then updated .mem_do_prefetch
  else if inputs.is_lb_lh_lw_lbu_lhu then true
  else if inputs.is_slli_srli_srai then updated .mem_do_rinst
  else if inputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
    updated .mem_do_prefetch
  else if inputs.is_sb_sh_sw then true
  else if inputs.is_sll_srl_sra then updated .mem_do_rinst
  else updated .mem_do_prefetch

def structuralState (inputs : Inputs) (updated : stateMap.Values) : stateMap.Values
  | .cpu_state => selectedPhase inputs
  | .mem_do_rinst => selectedRinst inputs updated
  | field => updated field

def structuralTransition (inputs : Inputs) (updated : stateMap.Values) : Transition :=
  simpleTransition (structuralState inputs updated)

set_option linter.unusedSimpArgs false in
theorem structuralTransition_eq_loadRs1Transition (inputs : Inputs)
    (updated : stateMap.Values) :
    structuralTransition inputs updated = loadRs1Transition inputs updated := by
  by_cases trap : inputs.instr_trap
  · simp [structuralTransition, loadRs1Transition, trap, simpleTransition]
    congr
    funext field
    cases field <;> simp [structuralState, selectedPhase, selectedRinst,
      SignalMap.set, trap]
  · simp [loadRs1Transition, trap]
    by_cases direct : inputs.is_lui_auipc_jal
    · simp [structuralTransition, direct, trap, simpleTransition]
      congr
      funext field
      cases field <;> simp [structuralState, selectedPhase, selectedRinst,
        SignalMap.set, direct, trap]
    · simp [direct]
      by_cases load : inputs.is_lb_lh_lw_lbu_lhu
      · simp [structuralTransition, load, direct, trap, simpleTransition]
        congr
        funext field
        cases field <;> simp [structuralState, selectedPhase, selectedRinst,
          SignalMap.set, load, direct, trap]
      · simp [load]
        by_cases immediateShift : inputs.is_slli_srli_srai
        · simp [structuralTransition, immediateShift, load, direct, trap,
            simpleTransition]
          congr
          funext field
          cases field <;> simp [structuralState, selectedPhase, selectedRinst,
            SignalMap.set, immediateShift, load, direct, trap]
        · simp [immediateShift]
          by_cases immediateAlu :
              inputs.is_jalr_addi_slti_sltiu_xori_ori_andi
          · simp [structuralTransition, immediateAlu, immediateShift, load,
              direct, trap, simpleTransition]
            congr
            funext field
            cases field <;> simp [structuralState, selectedPhase,
              selectedRinst, SignalMap.set, immediateAlu, immediateShift,
              load, direct, trap]
          · simp [immediateAlu]
            by_cases store : inputs.is_sb_sh_sw
            · simp [structuralTransition, store, immediateAlu, immediateShift,
                load, direct, trap, simpleTransition]
              congr
              funext field
              cases field <;> simp [structuralState, selectedPhase,
                selectedRinst, SignalMap.set, store, immediateAlu,
                immediateShift, load, direct, trap]
            · simp [store]
              by_cases regShift : inputs.is_sll_srl_sra
              · simp [structuralTransition, regShift, store, immediateAlu,
                  immediateShift, load, direct, trap, simpleTransition]
                congr
                funext field
                cases field <;> simp [structuralState, selectedPhase,
                  selectedRinst, SignalMap.set, regShift, store, immediateAlu,
                  immediateShift, load, direct, trap]
              · simp [structuralTransition, regShift, store, immediateAlu,
                  immediateShift, load, direct, trap, simpleTransition]
                congr
                funext field
                cases field <;> simp [structuralState, selectedPhase,
                  selectedRinst, SignalMap.set, regShift, store, immediateAlu,
                  immediateShift, load, direct, trap]

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
  have inputField (field : ControlInputs.Field) :
      (proposal.2 .inputsFields).outputs field = controlInputs.toValues field := by
    rw [inputsFieldsValue]
    cases field <;> rfl
  have instrTrapValue : (proposal.2 .inputsFields).outputs .instr_trap =
      controlInputs.instr_trap := by
    simpa [Inputs.toValues] using inputField .instr_trap
  have directSelectorValue :
      (proposal.2 .inputsFields).outputs .is_lui_auipc_jal =
        controlInputs.is_lui_auipc_jal := by
    simpa [Inputs.toValues] using inputField .is_lui_auipc_jal
  have loadSelectorValue :
      (proposal.2 .inputsFields).outputs .is_lb_lh_lw_lbu_lhu =
        controlInputs.is_lb_lh_lw_lbu_lhu := by
    simpa [Inputs.toValues] using inputField .is_lb_lh_lw_lbu_lhu
  have immediateShiftSelectorValue :
      (proposal.2 .inputsFields).outputs .is_slli_srli_srai =
        controlInputs.is_slli_srli_srai := by
    simpa [Inputs.toValues] using inputField .is_slli_srli_srai
  have immediateAluSelectorValue :
      (proposal.2 .inputsFields).outputs
          .is_jalr_addi_slti_sltiu_xori_ori_andi =
        controlInputs.is_jalr_addi_slti_sltiu_xori_ori_andi := by
    simpa [Inputs.toValues] using
      inputField .is_jalr_addi_slti_sltiu_xori_ori_andi
  have storeSelectorValue :
      (proposal.2 .inputsFields).outputs .is_sb_sh_sw =
        controlInputs.is_sb_sh_sw := by
    simpa [Inputs.toValues] using inputField .is_sb_sh_sw
  have regShiftSelectorValue :
      (proposal.2 .inputsFields).outputs .is_sll_srl_sra =
        controlInputs.is_sll_srl_sra := by
    simpa [Inputs.toValues] using inputField .is_sll_srl_sra

  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have trueValue := (Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).1.1 Primitives.ConstantRule.apply)
  have trapStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateTrap) _ _ _).mp
    ((childMatch .trapState).1.1 Primitives.ConstantRule.apply)
  have executeStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateExec) _ _ _).mp
    ((childMatch .executeState).1.1 Primitives.ConstantRule.apply)
  have loadStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdmem) _ _ _).mp
    ((childMatch .loadState).1.1 Primitives.ConstantRule.apply)
  have shiftStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateShift) _ _ _).mp
    ((childMatch .shiftState).1.1 Primitives.ConstantRule.apply)
  have storeStateValue := (Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateStmem) _ _ _).mp
    ((childMatch .storeState).1.1 Primitives.ConstantRule.apply)

  have regShiftPhaseValue : (proposal.2 .regShiftPhase).outputs .result =
      bif controlInputs.is_sll_srl_sra then stateBits cpuStateShift
        else stateBits cpuStateExec := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .regShiftPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [regShiftSelectorValue, executeStateValue, shiftStateValue] at equation
    exact equation
  have regShiftRinstValue : (proposal.2 .regShiftRinst).outputs .result =
      bif controlInputs.is_sll_srl_sra then updated .mem_do_rinst
        else updated .mem_do_prefetch := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .regShiftRinst).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [regShiftSelectorValue, updatedFieldsValue] at equation
    exact equation
  have storePhaseValue : (proposal.2 .storePhase).outputs .result =
      bif controlInputs.is_sb_sh_sw then stateBits cpuStateStmem
        else (proposal.2 .regShiftPhase).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .storePhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storeSelectorValue, storeStateValue] at equation
    exact equation
  have storeRinstValue : (proposal.2 .storeRinst).outputs .result =
      bif controlInputs.is_sb_sh_sw then true
        else (proposal.2 .regShiftRinst).outputs .result := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .storeRinst).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storeSelectorValue, trueValue] at equation
    exact equation
  have immediateAluPhaseValue : (proposal.2 .immediateAluPhase).outputs .result =
      bif controlInputs.is_jalr_addi_slti_sltiu_xori_ori_andi
        then stateBits cpuStateExec else (proposal.2 .storePhase).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .immediateAluPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [immediateAluSelectorValue,
      executeStateValue] at equation
    exact equation
  have immediateAluRinstValue : (proposal.2 .immediateAluRinst).outputs .result =
      bif controlInputs.is_jalr_addi_slti_sltiu_xori_ori_andi
        then updated .mem_do_prefetch else (proposal.2 .storeRinst).outputs .result := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .immediateAluRinst).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [immediateAluSelectorValue,
      updatedFieldsValue] at equation
    exact equation
  have immediateShiftPhaseValue :
      (proposal.2 .immediateShiftPhase).outputs .result =
        bif controlInputs.is_slli_srli_srai then stateBits cpuStateShift
          else (proposal.2 .immediateAluPhase).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .immediateShiftPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [immediateShiftSelectorValue, shiftStateValue] at equation
    exact equation
  have immediateShiftRinstValue :
      (proposal.2 .immediateShiftRinst).outputs .result =
        bif controlInputs.is_slli_srli_srai then updated .mem_do_rinst
          else (proposal.2 .immediateAluRinst).outputs .result := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .immediateShiftRinst).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [immediateShiftSelectorValue, updatedFieldsValue] at equation
    exact equation
  have loadPhaseValue : (proposal.2 .loadPhase).outputs .result =
      bif controlInputs.is_lb_lh_lw_lbu_lhu then stateBits cpuStateLdmem
        else (proposal.2 .immediateShiftPhase).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .loadPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [loadSelectorValue, loadStateValue] at equation
    exact equation
  have loadRinstValue : (proposal.2 .loadRinst).outputs .result =
      bif controlInputs.is_lb_lh_lw_lbu_lhu then true
        else (proposal.2 .immediateShiftRinst).outputs .result := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .loadRinst).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [loadSelectorValue, trueValue] at equation
    exact equation
  have directPhaseValue : (proposal.2 .directPhase).outputs .result =
      bif controlInputs.is_lui_auipc_jal then stateBits cpuStateExec
        else (proposal.2 .loadPhase).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .directPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [directSelectorValue, executeStateValue] at equation
    exact equation
  have directRinstValue : (proposal.2 .directRinst).outputs .result =
      bif controlInputs.is_lui_auipc_jal then updated .mem_do_prefetch
        else (proposal.2 .loadRinst).outputs .result := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .directRinst).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [directSelectorValue, updatedFieldsValue] at equation
    exact equation
  have trapPhaseValue : (proposal.2 .trapPhase).outputs .result =
      bif controlInputs.instr_trap then stateBits cpuStateTrap
        else (proposal.2 .directPhase).outputs .result := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 8 .bit)
      _ _ _ _ (childMatch .trapPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [instrTrapValue, trapStateValue] at equation
    exact equation
  have trapRinstValue : (proposal.2 .trapRinst).outputs .result =
      bif controlInputs.instr_trap then updated .mem_do_rinst
        else (proposal.2 .directRinst).outputs .result := by
    have equation := (Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .trapRinst).1.1 Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [instrTrapValue, updatedFieldsValue] at equation
    exact equation

  have selectedPhaseValue : (proposal.2 .trapPhase).outputs .result =
      selectedPhase controlInputs := by
    rw [trapPhaseValue, directPhaseValue, loadPhaseValue,
      immediateShiftPhaseValue, immediateAluPhaseValue, storePhaseValue,
      regShiftPhaseValue]
    cases trap : controlInputs.instr_trap <;>
      cases direct : controlInputs.is_lui_auipc_jal <;>
      cases load : controlInputs.is_lb_lh_lw_lbu_lhu <;>
      cases immediateShift : controlInputs.is_slli_srli_srai <;>
      cases immediateAlu :
        controlInputs.is_jalr_addi_slti_sltiu_xori_ori_andi <;>
      cases store : controlInputs.is_sb_sh_sw <;>
      cases regShift : controlInputs.is_sll_srl_sra <;>
      simp [selectedPhase, trap, direct, load, immediateShift, immediateAlu,
        store, regShift]
  have selectedRinstValue : (proposal.2 .trapRinst).outputs .result =
      selectedRinst controlInputs updated := by
    rw [trapRinstValue, directRinstValue, loadRinstValue,
      immediateShiftRinstValue, immediateAluRinstValue, storeRinstValue,
      regShiftRinstValue]
    cases trap : controlInputs.instr_trap <;>
      cases direct : controlInputs.is_lui_auipc_jal <;>
      cases load : controlInputs.is_lb_lh_lw_lbu_lhu <;>
      cases immediateShift : controlInputs.is_slli_srli_srai <;>
      cases immediateAlu :
        controlInputs.is_jalr_addi_slti_sltiu_xori_ori_andi <;>
      cases store : controlInputs.is_sb_sh_sw <;>
      cases regShift : controlInputs.is_sll_srl_sra <;>
      simp [selectedRinst, trap, direct, load, immediateShift, immediateAlu,
        store, regShift]

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
    rw [resultValue, structuralTransition_eq_loadRs1Transition]
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

end Silean.Examples.PicoRV.Control.LoadRs1Transition
