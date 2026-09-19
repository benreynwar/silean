import PicoRV.Datapath.DatapathMemoryUpdate
import PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Add.AddTheorems
import Silean.Modules.BitMux.BitMuxTheorems
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.VectorLayout.VectorLayoutTheorems
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace PicoRV.Datapath.MemoryUpdateCore

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Silean.Modules.Constant.certification .bit false,
  zeroWord := Silean.Modules.Constant.certification (.vector 32 .bit) (wordOfNat 0),
  notPrefetch := Silean.Primitives.notCertified.certification,
  progress := Silean.Primitives.orCertified.certification,
  active := Silean.Modules.BitMux.certification,
  notActive := Silean.Primitives.notCertified.certification,
  effectiveAddress := Silean.Modules.Add.certification 32,
  effectiveOp1 := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectedOp1 := Silean.Modules.Mux.certification (.vector 32 .bit),
  signedHalf := Silean.Modules.VectorLayout.certification 32 32 (signExtendLayout 16),
  signedByte := Silean.Modules.VectorLayout.certification 32 32 (signExtendLayout 8),
  selectByte := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectHalf := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectUnsigned := Silean.Modules.Mux.certification (.vector 32 .bit),
  loadDoneLeft := Silean.Primitives.andCertified.certification,
  loadDone := Silean.Primitives.andCertified.certification,
  selectedResult := Silean.Modules.Mux.certification (.vector 32 .bit),
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Silean.Modules.NamedTupleSplitter.Rule.apply,
    {.falseBit, .zeroWord} => Silean.Primitives.ConstantRule.apply,
    .notPrefetch => Silean.Primitives.NotRule.apply,
    .progress => Silean.Primitives.OrRule.apply,
    .active => Silean.Modules.BitMux.Rule.select,
    .notActive => Silean.Primitives.NotRule.apply,
    .effectiveAddress => Silean.Modules.Add.Rule.apply,
    {.effectiveOp1, .selectedOp1} => Silean.Modules.Mux.Rule.select,
    {.signedHalf, .signedByte} => Silean.Modules.VectorLayout.Rule.apply,
    {.selectByte, .selectHalf, .selectUnsigned} => Silean.Modules.Mux.Rule.select,
    .loadDoneLeft => Silean.Primitives.AndRule.apply,
    .loadDone => Silean.Primitives.AndRule.apply,
    .selectedResult => Silean.Modules.Mux.Rule.select,
    .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
  state := []

theorem sign_extend_16_layout (word : Word) :
    Silean.Modules.VectorLayout.apply (signExtendLayout 16) word = signExtended16 word := by
  funext index
  by_cases low : index.val < 16 <;>
    simp [Silean.Modules.VectorLayout.apply, signExtendLayout, signExtended16, low]

theorem sign_extend_8_layout (word : Word) :
    Silean.Modules.VectorLayout.apply (signExtendLayout 8) word = signExtended8 word := by
  funext index
  by_cases low : index.val < 8 <;>
    simp [Silean.Modules.VectorLayout.apply, signExtendLayout, signExtended8, low]

def structuralOp1 (isLoad : Bool) (inputs : Inputs)
    (current updated : stateMap.Values) : Word :=
  if inputs.mem_do_prefetch && !inputs.mem_done then updated .reg_op1
  else if !(if isLoad then inputs.mem_do_rdata else inputs.mem_do_wdata) then
    addWords (current .reg_op1) inputs.decoded_imm
  else updated .reg_op1

def structuralResult (isLoad : Bool) (inputs : Inputs)
    (updated : stateMap.Values) : Word :=
  if isLoad && !inputs.mem_do_prefetch && inputs.mem_done then loadResult inputs
  else updated .reg_out

def structuralState (isLoad : Bool) (inputs : Inputs)
    (current updated : stateMap.Values) : stateMap.Values
  | .reg_op1 => structuralOp1 isLoad inputs current updated
  | .reg_out => structuralResult isLoad inputs updated
  | field => updated field

theorem structuralState_eq_memoryNextState (isLoad : Bool) (inputs : Inputs)
    (current updated : stateMap.Values) :
    structuralState isLoad inputs current updated =
      memoryNextState isLoad inputs current updated := by
  cases isLoad <;> cases prefetch : inputs.mem_do_prefetch <;>
    cases done : inputs.mem_done <;> cases rdata : inputs.mem_do_rdata <;>
    cases wdata : inputs.mem_do_wdata <;> funext field <;> cases field <;>
    simp [structuralState, structuralOp1, structuralResult, memoryNextState,
      Silean.SignalMap.set, prefetch, done, rdata, wdata]

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let datapathInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let updated := stateMap.unpack (inputs .updated)
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      DatapathInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, current] using equation
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, updated] using equation
  have inputField (field : DatapathInputs.Field) :
      hierStep.childOutputs .inputsFields field = datapathInputs.toValues field := by
    exact (congrFun inputsFieldsValue field).trans
      (congrFun (Inputs.toValues_unpack _).symm field)
  have falseValue := (Silean.Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Silean.Primitives.ConstantRule.apply)
  have zeroValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 0) _ _ _).mp
    ((childMatch .zeroWord).ruleHolds Silean.Primitives.ConstantRule.apply)

  have notPrefetchValue : hierStep.childOutputs .notPrefetch .output =
      !datapathInputs.mem_do_prefetch := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notPrefetch).ruleHolds Silean.Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [inputField .mem_do_prefetch] at equation
    exact equation
  have progressValue : hierStep.childOutputs .progress .output =
      (!datapathInputs.mem_do_prefetch || datapathInputs.mem_done) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .progress).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [notPrefetchValue, inputField .mem_done] at equation
    exact equation
  have activeValue : hierStep.childOutputs .active .result =
      (bif inputs .isLoad then datapathInputs.mem_do_rdata
      else datapathInputs.mem_do_wdata) := by
    have equation := Silean.Modules.BitMux.result_of_allowed
      (childMatch .active).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [inputField .mem_do_rdata, inputField .mem_do_wdata] at equation
    change hierStep.childOutputs .active .result = bif inputs .isLoad
      then datapathInputs.mem_do_rdata else datapathInputs.mem_do_wdata at equation
    cases isLoad : inputs .isLoad <;>
      simp [isLoad] at equation ⊢ <;> exact equation
  have notActiveValue : hierStep.childOutputs .notActive .output =
      !(bif inputs .isLoad then datapathInputs.mem_do_rdata
      else datapathInputs.mem_do_wdata) := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notActive).ruleHolds Silean.Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [activeValue] at equation
    exact equation
  have addressValue : hierStep.childOutputs .effectiveAddress .result =
      addWords (current .reg_op1) datapathInputs.decoded_imm := by
    have equation :=
      (Silean.Modules.Add.Behavior.of_allowed 32
        (childMatch .effectiveAddress).allowed).result
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue, inputField .decoded_imm, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation
  have effectiveOp1Value : hierStep.childOutputs .effectiveOp1 .result =
      (if !(bif inputs .isLoad then datapathInputs.mem_do_rdata
        else datapathInputs.mem_do_wdata) then
        addWords (current .reg_op1) datapathInputs.decoded_imm
      else updated .reg_op1) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .effectiveOp1).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [notActiveValue, addressValue, updatedFieldsValue] at equation
    cases isLoad : inputs .isLoad <;> cases rdata : datapathInputs.mem_do_rdata <;>
      cases wdata : datapathInputs.mem_do_wdata <;>
      simp [isLoad, rdata, wdata] at equation ⊢ <;> exact equation
  have selectedOp1Value : hierStep.childOutputs .selectedOp1 .result =
      structuralOp1 (inputs .isLoad) datapathInputs current updated := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectedOp1).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [progressValue, effectiveOp1Value, updatedFieldsValue] at equation
    cases prefetch : datapathInputs.mem_do_prefetch <;>
      cases done : datapathInputs.mem_done <;> cases isLoad : inputs .isLoad <;>
      cases rdata : datapathInputs.mem_do_rdata <;>
      cases wdata : datapathInputs.mem_do_wdata <;>
      simp [structuralOp1, prefetch, done, isLoad, rdata, wdata] at equation ⊢ <;>
      exact equation

  have signedHalfValue : hierStep.childOutputs .signedHalf .output =
      signExtended16 datapathInputs.mem_rdata_word := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 32
      (signExtendLayout 16) (childMatch .signedHalf).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [inputField .mem_rdata_word, sign_extend_16_layout] at equation
    exact equation
  have signedByteValue : hierStep.childOutputs .signedByte .output =
      signExtended8 datapathInputs.mem_rdata_word := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 32
      (signExtendLayout 8) (childMatch .signedByte).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [inputField .mem_rdata_word, sign_extend_8_layout] at equation
    exact equation
  have byteValue : hierStep.childOutputs .selectByte .result =
      (if datapathInputs.latched_is_lb then signExtended8 datapathInputs.mem_rdata_word
      else wordOfNat 0) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectByte).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [inputField .latched_is_lb, zeroValue, signedByteValue] at equation
    simp only [Inputs.toValues] at equation
    cases byte : datapathInputs.latched_is_lb <;>
      simp [byte] at equation ⊢ <;> exact equation
  have halfValue : hierStep.childOutputs .selectHalf .result =
      (if datapathInputs.latched_is_lh then signExtended16 datapathInputs.mem_rdata_word
      else if datapathInputs.latched_is_lb then signExtended8 datapathInputs.mem_rdata_word
      else wordOfNat 0) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectHalf).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [inputField .latched_is_lh, byteValue, signedHalfValue] at equation
    simp only [Inputs.toValues] at equation
    cases half : datapathInputs.latched_is_lh <;>
      simp [half] at equation ⊢ <;> exact equation
  have loadResultValue : hierStep.childOutputs .selectUnsigned .result =
      loadResult datapathInputs := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectUnsigned).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [inputField .latched_is_lu, inputField .mem_rdata_word,
      halfValue] at equation
    simp only [Inputs.toValues] at equation
    cases unsigned : datapathInputs.latched_is_lu <;>
      cases half : datapathInputs.latched_is_lh <;>
      cases byte : datapathInputs.latched_is_lb <;>
      simp [loadResult, unsigned, half, byte] at equation ⊢ <;> exact equation

  have loadDoneLeftValue : hierStep.childOutputs .loadDoneLeft .output =
      (inputs .isLoad && !datapathInputs.mem_do_prefetch) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .loadDoneLeft).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [notPrefetchValue] at equation
    exact equation
  have loadDoneValue : hierStep.childOutputs .loadDone .output =
      (inputs .isLoad && !datapathInputs.mem_do_prefetch &&
        datapathInputs.mem_done) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .loadDone).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [loadDoneLeftValue, inputField .mem_done] at equation
    exact equation
  have selectedResultValue : hierStep.childOutputs .selectedResult .result =
      structuralResult (inputs .isLoad) datapathInputs updated := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectedResult).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [loadDoneValue, updatedFieldsValue, loadResultValue] at equation
    cases isLoad : inputs .isLoad <;> cases prefetch : datapathInputs.mem_do_prefetch <;>
      cases done : datapathInputs.mem_done <;>
      simp [structuralResult, isLoad, prefetch, done] at equation ⊢ <;>
      exact equation

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result =
        structuralState (inputs .isLoad) datapathInputs current updated := by
    funext field
    cases field
    · change hierStep.childOutputs .updatedFields .reg_pc = _
      exact congrFun updatedFieldsValue .reg_pc
    · change hierStep.childOutputs .updatedFields .reg_next_pc = _
      exact congrFun updatedFieldsValue .reg_next_pc
    · change hierStep.childOutputs .selectedOp1 .result = _; exact selectedOp1Value
    · change hierStep.childOutputs .updatedFields .reg_op2 = _
      exact congrFun updatedFieldsValue .reg_op2
    · change hierStep.childOutputs .selectedResult .result = _
      exact selectedResultValue
    · change hierStep.childOutputs .updatedFields .reg_sh = _
      exact congrFun updatedFieldsValue .reg_sh
    · change hierStep.childOutputs .updatedFields .alu_out_q = _
      exact congrFun updatedFieldsValue .alu_out_q
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (MemoryUpdateCore.outputState inputs) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs, structuralState_eq_memoryNextState] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .result .value by
      exact satisfies.1 .state]
    exact resultValue
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

end PicoRV.Datapath.MemoryUpdateCore

namespace PicoRV.Datapath.StoreUpdate

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  isLoad := Silean.Modules.Constant.certification .bit false,
  update := MemoryUpdateCore.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .isLoad => Silean.Primitives.ConstantRule.apply,
    .update => MemoryUpdateCore.Rule.apply]
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec
  have isLoadValue := (Silean.Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .isLoad).ruleHolds Silean.Primitives.ConstantRule.apply)
  have updateInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .update = (fun
        | .isLoad => false
        | .inputs => inputs .inputs
        | .current => inputs .current
        | .updated => inputs .updated) := by
    funext port
    cases port
    · change hierStep.childOutputs .isLoad .output = false
      exact isLoadValue
    · rfl
    · rfl
    · rfl
  have updateValue : hierStep.childOutputs .update .state =
      stateMap.pack (StateUpdate.outputState (memoryNextState false) inputs) := by
    have equation := (MemoryUpdateCore.outputRule_holds_iff _ _ _).mp
      ((childMatch .update).ruleHolds MemoryUpdateCore.Rule.apply)
    rw [updateInputs] at equation
    simpa [MemoryUpdateCore.outputState, StateUpdate.outputState] using equation
  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .update .state by
      exact satisfies.1 .state]
    exact updateValue
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

end PicoRV.Datapath.StoreUpdate

namespace PicoRV.Datapath.LoadUpdate

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  isLoad := Silean.Modules.Constant.certification .bit true,
  update := MemoryUpdateCore.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .isLoad => Silean.Primitives.ConstantRule.apply,
    .update => MemoryUpdateCore.Rule.apply]
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec
  have isLoadValue := (Silean.Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .isLoad).ruleHolds Silean.Primitives.ConstantRule.apply)
  have updateInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .update = (fun
        | .isLoad => true
        | .inputs => inputs .inputs
        | .current => inputs .current
        | .updated => inputs .updated) := by
    funext port
    cases port
    · change hierStep.childOutputs .isLoad .output = true
      exact isLoadValue
    · rfl
    · rfl
    · rfl
  have updateValue : hierStep.childOutputs .update .state =
      stateMap.pack (StateUpdate.outputState (memoryNextState true) inputs) := by
    have equation := (MemoryUpdateCore.outputRule_holds_iff _ _ _).mp
      ((childMatch .update).ruleHolds MemoryUpdateCore.Rule.apply)
    rw [updateInputs] at equation
    simpa [MemoryUpdateCore.outputState, StateUpdate.outputState] using equation
  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .update .state by
      exact satisfies.1 .state]
    exact updateValue
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

end PicoRV.Datapath.LoadUpdate
