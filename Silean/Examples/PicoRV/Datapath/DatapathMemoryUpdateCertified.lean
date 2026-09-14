import Silean.Examples.PicoRV.Datapath.DatapathMemoryUpdate
import Silean.Examples.PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Add.Add
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Modules.VectorLayout.VectorLayoutCertified
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Datapath.MemoryUpdateCore

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  zeroWord := Modules.Constant.certification (.vector 32 .bit) (wordOfNat 0),
  notPrefetch := Primitives.notCertified.certification,
  progress := Primitives.orCertified.certification,
  active := Modules.Mux.certification .bit,
  notActive := Primitives.notCertified.certification,
  effectiveAddress := Modules.Add.certification 32,
  effectiveOp1 := Modules.Mux.certification (.vector 32 .bit),
  selectedOp1 := Modules.Mux.certification (.vector 32 .bit),
  signedHalf := Modules.VectorLayout.certification 32 32 (signExtendLayout 16),
  signedByte := Modules.VectorLayout.certification 32 32 (signExtendLayout 8),
  selectByte := Modules.Mux.certification (.vector 32 .bit),
  selectHalf := Modules.Mux.certification (.vector 32 .bit),
  selectUnsigned := Modules.Mux.certification (.vector 32 .bit),
  loadDoneLeft := Primitives.andCertified.certification,
  loadDone := Primitives.andCertified.certification,
  selectedResult := Modules.Mux.certification (.vector 32 .bit),
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Modules.NamedTupleSplitter.Rule.apply,
    {.falseBit, .zeroWord} => Primitives.ConstantRule.apply,
    .notPrefetch => Primitives.NotRule.apply,
    .progress => Primitives.OrRule.apply,
    .active => Modules.Mux.Rule.select,
    .notActive => Primitives.NotRule.apply,
    .effectiveAddress => Modules.Add.Rule.apply,
    {.effectiveOp1, .selectedOp1} => Modules.Mux.Rule.select,
    {.signedHalf, .signedByte} => Modules.VectorLayout.Rule.apply,
    {.selectByte, .selectHalf, .selectUnsigned} => Modules.Mux.Rule.select,
    .loadDoneLeft => Primitives.AndRule.apply,
    .loadDone => Primitives.AndRule.apply,
    .selectedResult => Modules.Mux.Rule.select,
    .result => Modules.NamedTupleCombiner.Rule.apply]
  state := []

theorem sign_extend_16_layout (word : Word) :
    Modules.VectorLayout.apply (signExtendLayout 16) word = signExtended16 word := by
  funext index
  by_cases low : index.val < 16 <;>
    simp [Modules.VectorLayout.apply, signExtendLayout, signExtended16, low]

theorem sign_extend_8_layout (word : Word) :
    Modules.VectorLayout.apply (signExtendLayout 8) word = signExtended8 word := by
  funext index
  by_cases low : index.val < 8 <;>
    simp [Modules.VectorLayout.apply, signExtendLayout, signExtended8, low]

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
      SignalMap.set, prefetch, done, rdata, wdata]

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

  let datapathInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let updated := stateMap.unpack (inputs .updated)
  have inputsFieldsValue : (proposal.2 .inputsFields).outputs =
      DatapathInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have currentFieldsValue : (proposal.2 .currentFields).outputs = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, current] using equation
  have updatedFieldsValue : (proposal.2 .updatedFields).outputs = updated := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, updated] using equation
  have inputField (field : DatapathInputs.Field) :
      (proposal.2 .inputsFields).outputs field = datapathInputs.toValues field := by
    rw [inputsFieldsValue]
    cases field <;> rfl
  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have zeroValue := (Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 0) _ _ _).mp
    ((childMatch .zeroWord).1.1 Primitives.ConstantRule.apply)

  have notPrefetchValue : (proposal.2 .notPrefetch).outputs .output =
      !datapathInputs.mem_do_prefetch := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notPrefetch).1.1 Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .mem_do_prefetch] at equation
    exact equation
  have progressValue : (proposal.2 .progress).outputs .output =
      (!datapathInputs.mem_do_prefetch || datapathInputs.mem_done) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .progress).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [notPrefetchValue, inputField .mem_done] at equation
    exact equation
  have activeValue : (proposal.2 .active).outputs .result =
      (bif inputs .isLoad then datapathInputs.mem_do_rdata
      else datapathInputs.mem_do_wdata) := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit
      _ _ _ _ (childMatch .active).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .mem_do_rdata, inputField .mem_do_wdata] at equation
    cases isLoad : inputs .isLoad <;> simp [isLoad] at equation ⊢ <;> exact equation
  have notActiveValue : (proposal.2 .notActive).outputs .output =
      !(bif inputs .isLoad then datapathInputs.mem_do_rdata
      else datapathInputs.mem_do_wdata) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notActive).1.1 Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [activeValue] at equation
    exact equation
  have addressValue : (proposal.2 .effectiveAddress).outputs .result =
      addWords (current .reg_op1) datapathInputs.decoded_imm := by
    have equation := Modules.Add.result_of_evaluatesTo 32
      _ _ _ _ (childMatch .effectiveAddress).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, inputField .decoded_imm, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation
  have effectiveOp1Value : (proposal.2 .effectiveOp1).outputs .result =
      (if !(bif inputs .isLoad then datapathInputs.mem_do_rdata
        else datapathInputs.mem_do_wdata) then
        addWords (current .reg_op1) datapathInputs.decoded_imm
      else updated .reg_op1) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .effectiveOp1).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [notActiveValue, addressValue, updatedFieldsValue] at equation
    cases isLoad : inputs .isLoad <;> cases rdata : datapathInputs.mem_do_rdata <;>
      cases wdata : datapathInputs.mem_do_wdata <;>
      simp [isLoad, rdata, wdata] at equation ⊢ <;> exact equation
  have selectedOp1Value : (proposal.2 .selectedOp1).outputs .result =
      structuralOp1 (inputs .isLoad) datapathInputs current updated := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectedOp1).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [progressValue, effectiveOp1Value, updatedFieldsValue] at equation
    cases prefetch : datapathInputs.mem_do_prefetch <;>
      cases done : datapathInputs.mem_done <;> cases isLoad : inputs .isLoad <;>
      cases rdata : datapathInputs.mem_do_rdata <;>
      cases wdata : datapathInputs.mem_do_wdata <;>
      simp [structuralOp1, prefetch, done, isLoad, rdata, wdata] at equation ⊢ <;>
      exact equation

  have signedHalfValue : (proposal.2 .signedHalf).outputs .output =
      signExtended16 datapathInputs.mem_rdata_word := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 32
      (signExtendLayout 16) _ _ _ _ (childMatch .signedHalf).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .mem_rdata_word, sign_extend_16_layout] at equation
    exact equation
  have signedByteValue : (proposal.2 .signedByte).outputs .output =
      signExtended8 datapathInputs.mem_rdata_word := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 32
      (signExtendLayout 8) _ _ _ _ (childMatch .signedByte).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .mem_rdata_word, sign_extend_8_layout] at equation
    exact equation
  have byteValue : (proposal.2 .selectByte).outputs .result =
      (if datapathInputs.latched_is_lb then signExtended8 datapathInputs.mem_rdata_word
      else wordOfNat 0) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectByte).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .latched_is_lb, zeroValue, signedByteValue] at equation
    simp only [Inputs.toValues] at equation
    cases byte : datapathInputs.latched_is_lb <;>
      simp [byte] at equation ⊢ <;> exact equation
  have halfValue : (proposal.2 .selectHalf).outputs .result =
      (if datapathInputs.latched_is_lh then signExtended16 datapathInputs.mem_rdata_word
      else if datapathInputs.latched_is_lb then signExtended8 datapathInputs.mem_rdata_word
      else wordOfNat 0) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectHalf).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .latched_is_lh, byteValue, signedHalfValue] at equation
    simp only [Inputs.toValues] at equation
    cases half : datapathInputs.latched_is_lh <;>
      simp [half] at equation ⊢ <;> exact equation
  have loadResultValue : (proposal.2 .selectUnsigned).outputs .result =
      loadResult datapathInputs := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectUnsigned).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .latched_is_lu, inputField .mem_rdata_word,
      halfValue] at equation
    simp only [Inputs.toValues] at equation
    cases unsigned : datapathInputs.latched_is_lu <;>
      cases half : datapathInputs.latched_is_lh <;>
      cases byte : datapathInputs.latched_is_lb <;>
      simp [loadResult, unsigned, half, byte] at equation ⊢ <;> exact equation

  have loadDoneLeftValue : (proposal.2 .loadDoneLeft).outputs .output =
      (inputs .isLoad && !datapathInputs.mem_do_prefetch) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .loadDoneLeft).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [notPrefetchValue] at equation
    exact equation
  have loadDoneValue : (proposal.2 .loadDone).outputs .output =
      (inputs .isLoad && !datapathInputs.mem_do_prefetch &&
        datapathInputs.mem_done) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .loadDone).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [loadDoneLeftValue, inputField .mem_done] at equation
    exact equation
  have selectedResultValue : (proposal.2 .selectedResult).outputs .result =
      structuralResult (inputs .isLoad) datapathInputs updated := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectedResult).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [loadDoneValue, updatedFieldsValue, loadResultValue] at equation
    cases isLoad : inputs .isLoad <;> cases prefetch : datapathInputs.mem_do_prefetch <;>
      cases done : datapathInputs.mem_done <;>
      simp [structuralResult, isLoad, prefetch, done] at equation ⊢ <;>
      exact equation

  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result =
        structuralState (inputs .isLoad) datapathInputs current updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, structuralState]
    · simpa using congrFun updatedFieldsValue .reg_pc
    · simpa using congrFun updatedFieldsValue .reg_next_pc
    · exact selectedOp1Value
    · simpa using congrFun updatedFieldsValue .reg_op2
    · exact selectedResultValue
    · simpa using congrFun updatedFieldsValue .reg_sh
    · simpa using congrFun updatedFieldsValue .alu_out_q
  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack (MemoryUpdateCore.outputState inputs) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs, structuralState_eq_memoryNextState] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    rw [show proposal.outputs .state = (proposal.2 .result).outputs .value by
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Datapath.MemoryUpdateCore

namespace Silean.Examples.PicoRV.Datapath.StoreUpdate

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  isLoad := Modules.Constant.certification .bit false,
  update := MemoryUpdateCore.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .isLoad => Primitives.ConstantRule.apply,
    .update => MemoryUpdateCore.Rule.apply]
  state := []

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
  have isLoadValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .isLoad).1.1 Primitives.ConstantRule.apply)
  have updateInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .update = (fun
        | .isLoad => false
        | .inputs => inputs .inputs
        | .current => inputs .current
        | .updated => inputs .updated) := by
    funext port
    cases port <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, EndpointContext.moduleInput,
        SignalSource.value]
    exact isLoadValue
  have updateValue : (proposal.2 .update).outputs .state =
      stateMap.pack (StateUpdate.outputState (memoryNextState false) inputs) := by
    have equation := (MemoryUpdateCore.outputRule_holds_iff _ _ _).mp
      ((childMatch .update).1.1 MemoryUpdateCore.Rule.apply)
    rw [updateInputs] at equation
    simpa [MemoryUpdateCore.outputState, StateUpdate.outputState] using equation
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    rw [show proposal.outputs .state = (proposal.2 .update).outputs .state by
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Datapath.StoreUpdate

namespace Silean.Examples.PicoRV.Datapath.LoadUpdate

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  isLoad := Modules.Constant.certification .bit true,
  update := MemoryUpdateCore.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .isLoad => Primitives.ConstantRule.apply,
    .update => MemoryUpdateCore.Rule.apply]
  state := []

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
  have isLoadValue := (Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .isLoad).1.1 Primitives.ConstantRule.apply)
  have updateInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .update = (fun
        | .isLoad => true
        | .inputs => inputs .inputs
        | .current => inputs .current
        | .updated => inputs .updated) := by
    funext port
    cases port <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, EndpointContext.moduleInput,
        SignalSource.value]
    exact isLoadValue
  have updateValue : (proposal.2 .update).outputs .state =
      stateMap.pack (StateUpdate.outputState (memoryNextState true) inputs) := by
    have equation := (MemoryUpdateCore.outputRule_holds_iff _ _ _).mp
      ((childMatch .update).1.1 MemoryUpdateCore.Rule.apply)
    rw [updateInputs] at equation
    simpa [MemoryUpdateCore.outputState, StateUpdate.outputState] using equation
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    rw [show proposal.outputs .state = (proposal.2 .update).outputs .state by
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Datapath.LoadUpdate
