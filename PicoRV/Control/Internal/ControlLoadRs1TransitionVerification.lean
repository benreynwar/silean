import PicoRV.Control.ControlLoadRs1Transition
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.BitMux.BitMuxTheorems
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace PicoRV.Control.LoadRs1Transition

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Silean.Modules.Constant.certification .bit false,
  trueBit := Silean.Modules.Constant.certification .bit true,
  trapState := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateTrap),
  executeState := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateExec),
  loadState := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateLdmem),
  shiftState := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateShift),
  storeState := Silean.Modules.Constant.certification (.vector 8 .bit)
    (stateBits cpuStateStmem),
  regShiftPhase := Silean.Modules.Mux.certification (.vector 8 .bit),
  regShiftRinst := Silean.Modules.BitMux.certification,
  storePhase := Silean.Modules.Mux.certification (.vector 8 .bit),
  storeRinst := Silean.Modules.BitMux.certification,
  immediateAluPhase := Silean.Modules.Mux.certification (.vector 8 .bit),
  immediateAluRinst := Silean.Modules.BitMux.certification,
  immediateShiftPhase := Silean.Modules.Mux.certification (.vector 8 .bit),
  immediateShiftRinst := Silean.Modules.BitMux.certification,
  loadPhase := Silean.Modules.Mux.certification (.vector 8 .bit),
  loadRinst := Silean.Modules.BitMux.certification,
  directPhase := Silean.Modules.Mux.certification (.vector 8 .bit),
  directRinst := Silean.Modules.BitMux.certification,
  trapPhase := Silean.Modules.Mux.certification (.vector 8 .bit),
  trapRinst := Silean.Modules.BitMux.certification,
  resultState := Silean.Modules.NamedTupleCombiner.certification stateMap,
  result := Silean.Modules.NamedTupleCombiner.certification TransitionValue.signalMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .updatedFields} => Silean.Modules.NamedTupleSplitter.Rule.apply,
        {.falseBit, .trueBit, .trapState, .executeState, .loadState,
          .shiftState, .storeState} => Silean.Primitives.ConstantRule.apply,
        .regShiftPhase => Silean.Modules.Mux.Rule.select,
        .regShiftRinst => Silean.Modules.BitMux.Rule.select,
        .storePhase => Silean.Modules.Mux.Rule.select,
        .storeRinst => Silean.Modules.BitMux.Rule.select,
        .immediateAluPhase => Silean.Modules.Mux.Rule.select,
        .immediateAluRinst => Silean.Modules.BitMux.Rule.select,
        .immediateShiftPhase => Silean.Modules.Mux.Rule.select,
        .immediateShiftRinst => Silean.Modules.BitMux.Rule.select,
        .loadPhase => Silean.Modules.Mux.Rule.select,
        .loadRinst => Silean.Modules.BitMux.Rule.select,
        .directPhase => Silean.Modules.Mux.Rule.select,
        .directRinst => Silean.Modules.BitMux.Rule.select,
        .trapPhase => Silean.Modules.Mux.Rule.select,
        .trapRinst => Silean.Modules.BitMux.Rule.select,
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
      Silean.SignalMap.set, trap]
  · simp [loadRs1Transition, trap]
    by_cases direct : inputs.is_lui_auipc_jal
    · simp [structuralTransition, direct, trap, simpleTransition]
      congr
      funext field
      cases field <;> simp [structuralState, selectedPhase, selectedRinst,
        Silean.SignalMap.set, direct, trap]
    · simp [direct]
      by_cases load : inputs.is_lb_lh_lw_lbu_lhu
      · simp [structuralTransition, load, direct, trap, simpleTransition]
        congr
        funext field
        cases field <;> simp [structuralState, selectedPhase, selectedRinst,
          Silean.SignalMap.set, load, direct, trap]
      · simp [load]
        by_cases immediateShift : inputs.is_slli_srli_srai
        · simp [structuralTransition, immediateShift, load, direct, trap,
            simpleTransition]
          congr
          funext field
          cases field <;> simp [structuralState, selectedPhase, selectedRinst,
            Silean.SignalMap.set, immediateShift, load, direct, trap]
        · simp [immediateShift]
          by_cases immediateAlu :
              inputs.is_jalr_addi_slti_sltiu_xori_ori_andi
          · simp [structuralTransition, immediateAlu, immediateShift, load,
              direct, trap, simpleTransition]
            congr
            funext field
            cases field <;> simp [structuralState, selectedPhase,
              selectedRinst, Silean.SignalMap.set, immediateAlu, immediateShift,
              load, direct, trap]
          · simp [immediateAlu]
            by_cases store : inputs.is_sb_sh_sw
            · simp [structuralTransition, store, immediateAlu, immediateShift,
                load, direct, trap, simpleTransition]
              congr
              funext field
              cases field <;> simp [structuralState, selectedPhase,
                selectedRinst, Silean.SignalMap.set, store, immediateAlu,
                immediateShift, load, direct, trap]
            · simp [store]
              by_cases regShift : inputs.is_sll_srl_sra
              · simp [structuralTransition, regShift, store, immediateAlu,
                  immediateShift, load, direct, trap, simpleTransition]
                congr
                funext field
                cases field <;> simp [structuralState, selectedPhase,
                  selectedRinst, Silean.SignalMap.set, regShift, store, immediateAlu,
                  immediateShift, load, direct, trap]
              · simp [structuralTransition, regShift, store, immediateAlu,
                  immediateShift, load, direct, trap, simpleTransition]
                congr
                funext field
                cases field <;> simp [structuralState, selectedPhase,
                  selectedRinst, Silean.SignalMap.set, regShift, store, immediateAlu,
                  immediateShift, load, direct, trap]

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
    exact (congrFun inputsFieldsValue field).trans
      (congrFun (Inputs.toValues_unpack _).symm field)
  have instrTrapValue : hierStep.childOutputs .inputsFields .instr_trap =
      controlInputs.instr_trap := by
    simpa [Inputs.toValues] using inputField .instr_trap
  have directSelectorValue :
      hierStep.childOutputs .inputsFields .is_lui_auipc_jal =
        controlInputs.is_lui_auipc_jal := by
    simpa [Inputs.toValues] using inputField .is_lui_auipc_jal
  have loadSelectorValue :
      hierStep.childOutputs .inputsFields .is_lb_lh_lw_lbu_lhu =
        controlInputs.is_lb_lh_lw_lbu_lhu := by
    simpa [Inputs.toValues] using inputField .is_lb_lh_lw_lbu_lhu
  have immediateShiftSelectorValue :
      hierStep.childOutputs .inputsFields .is_slli_srli_srai =
        controlInputs.is_slli_srli_srai := by
    simpa [Inputs.toValues] using inputField .is_slli_srli_srai
  have immediateAluSelectorValue :
      hierStep.childOutputs .inputsFields
          .is_jalr_addi_slti_sltiu_xori_ori_andi =
        controlInputs.is_jalr_addi_slti_sltiu_xori_ori_andi := by
    simpa [Inputs.toValues] using
      inputField .is_jalr_addi_slti_sltiu_xori_ori_andi
  have storeSelectorValue :
      hierStep.childOutputs .inputsFields .is_sb_sh_sw =
        controlInputs.is_sb_sh_sw := by
    simpa [Inputs.toValues] using inputField .is_sb_sh_sw
  have regShiftSelectorValue :
      hierStep.childOutputs .inputsFields .is_sll_srl_sra =
        controlInputs.is_sll_srl_sra := by
    simpa [Inputs.toValues] using inputField .is_sll_srl_sra

  have falseValue := (Silean.Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Silean.Primitives.ConstantRule.apply)
  have trueValue := (Silean.Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).ruleHolds Silean.Primitives.ConstantRule.apply)
  have trapStateValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateTrap) _ _ _).mp
    ((childMatch .trapState).ruleHolds Silean.Primitives.ConstantRule.apply)
  have executeStateValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateExec) _ _ _).mp
    ((childMatch .executeState).ruleHolds Silean.Primitives.ConstantRule.apply)
  have loadStateValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateLdmem) _ _ _).mp
    ((childMatch .loadState).ruleHolds Silean.Primitives.ConstantRule.apply)
  have shiftStateValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateShift) _ _ _).mp
    ((childMatch .shiftState).ruleHolds Silean.Primitives.ConstantRule.apply)
  have storeStateValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 8 .bit) (stateBits cpuStateStmem) _ _ _).mp
    ((childMatch .storeState).ruleHolds Silean.Primitives.ConstantRule.apply)

  have regShiftPhaseValue : hierStep.childOutputs .regShiftPhase .result =
      bif controlInputs.is_sll_srl_sra then stateBits cpuStateShift
        else stateBits cpuStateExec := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 8 .bit)
      (childMatch .regShiftPhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr regShiftSelectorValue
      shiftStateValue executeStateValue)
  have regShiftRinstValue : hierStep.childOutputs .regShiftRinst .result =
      bif controlInputs.is_sll_srl_sra then updated .mem_do_rinst
        else updated .mem_do_prefetch := by
    have equation := (Silean.Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .regShiftRinst).ruleHolds Silean.Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr regShiftSelectorValue
      (congrFun updatedFieldsValue .mem_do_rinst)
      (congrFun updatedFieldsValue .mem_do_prefetch))
  have storePhaseValue : hierStep.childOutputs .storePhase .result =
      bif controlInputs.is_sb_sh_sw then stateBits cpuStateStmem
        else hierStep.childOutputs .regShiftPhase .result := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 8 .bit)
      (childMatch .storePhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr storeSelectorValue
      storeStateValue (Eq.refl _))
  have storeRinstValue : hierStep.childOutputs .storeRinst .result =
      bif controlInputs.is_sb_sh_sw then true
        else hierStep.childOutputs .regShiftRinst .result := by
    have equation := (Silean.Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .storeRinst).ruleHolds Silean.Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr storeSelectorValue trueValue (Eq.refl _))
  have immediateAluPhaseValue : hierStep.childOutputs .immediateAluPhase .result =
      bif controlInputs.is_jalr_addi_slti_sltiu_xori_ori_andi
        then stateBits cpuStateExec else hierStep.childOutputs .storePhase .result := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 8 .bit)
      (childMatch .immediateAluPhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr immediateAluSelectorValue
      executeStateValue (Eq.refl _))
  have immediateAluRinstValue : hierStep.childOutputs .immediateAluRinst .result =
      bif controlInputs.is_jalr_addi_slti_sltiu_xori_ori_andi
        then updated .mem_do_prefetch else hierStep.childOutputs .storeRinst .result := by
    have equation := (Silean.Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .immediateAluRinst).ruleHolds Silean.Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr immediateAluSelectorValue
      (congrFun updatedFieldsValue .mem_do_prefetch) (Eq.refl _))
  have immediateShiftPhaseValue :
      hierStep.childOutputs .immediateShiftPhase .result =
        bif controlInputs.is_slli_srli_srai then stateBits cpuStateShift
          else hierStep.childOutputs .immediateAluPhase .result := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 8 .bit)
      (childMatch .immediateShiftPhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr immediateShiftSelectorValue
      shiftStateValue (Eq.refl _))
  have immediateShiftRinstValue :
      hierStep.childOutputs .immediateShiftRinst .result =
        bif controlInputs.is_slli_srli_srai then updated .mem_do_rinst
          else hierStep.childOutputs .immediateAluRinst .result := by
    have equation := (Silean.Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .immediateShiftRinst).ruleHolds Silean.Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr immediateShiftSelectorValue
      (congrFun updatedFieldsValue .mem_do_rinst) (Eq.refl _))
  have loadPhaseValue : hierStep.childOutputs .loadPhase .result =
      bif controlInputs.is_lb_lh_lw_lbu_lhu then stateBits cpuStateLdmem
        else hierStep.childOutputs .immediateShiftPhase .result := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 8 .bit)
      (childMatch .loadPhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr loadSelectorValue
      loadStateValue (Eq.refl _))
  have loadRinstValue : hierStep.childOutputs .loadRinst .result =
      bif controlInputs.is_lb_lh_lw_lbu_lhu then true
        else hierStep.childOutputs .immediateShiftRinst .result := by
    have equation := (Silean.Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .loadRinst).ruleHolds Silean.Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr loadSelectorValue trueValue (Eq.refl _))
  have directPhaseValue : hierStep.childOutputs .directPhase .result =
      bif controlInputs.is_lui_auipc_jal then stateBits cpuStateExec
        else hierStep.childOutputs .loadPhase .result := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 8 .bit)
      (childMatch .directPhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr directSelectorValue
      executeStateValue (Eq.refl _))
  have directRinstValue : hierStep.childOutputs .directRinst .result =
      bif controlInputs.is_lui_auipc_jal then updated .mem_do_prefetch
        else hierStep.childOutputs .loadRinst .result := by
    have equation := (Silean.Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .directRinst).ruleHolds Silean.Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr directSelectorValue
      (congrFun updatedFieldsValue .mem_do_prefetch) (Eq.refl _))
  have trapPhaseValue : hierStep.childOutputs .trapPhase .result =
      bif controlInputs.instr_trap then stateBits cpuStateTrap
        else hierStep.childOutputs .directPhase .result := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 8 .bit)
      (childMatch .trapPhase).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr instrTrapValue
      trapStateValue (Eq.refl _))
  have trapRinstValue : hierStep.childOutputs .trapRinst .result =
      bif controlInputs.instr_trap then updated .mem_do_rinst
        else hierStep.childOutputs .directRinst .result := by
    have equation := (Silean.Modules.BitMux.selectRule_holds_iff _ _ _).mp
      ((childMatch .trapRinst).ruleHolds Silean.Modules.BitMux.Rule.select)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (bif_congr instrTrapValue
      (congrFun updatedFieldsValue .mem_do_rinst) (Eq.refl _))

  have selectedPhaseValue : hierStep.childOutputs .trapPhase .result =
      selectedPhase controlInputs := by
    rw [trapPhaseValue, directPhaseValue, loadPhaseValue,
      immediateShiftPhaseValue, immediateAluPhaseValue, storePhaseValue,
      regShiftPhaseValue]
    simp only [selectedPhase, Bool.cond_eq_ite]
  have selectedRinstValue : hierStep.childOutputs .trapRinst .result =
      selectedRinst controlInputs updated := by
    rw [trapRinstValue, directRinstValue, loadRinstValue,
      immediateShiftRinstValue, immediateAluRinstValue, storeRinstValue,
      regShiftRinstValue]
    simp only [selectedRinst, Bool.cond_eq_ite]
    rfl

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
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Control.LoadRs1Transition
