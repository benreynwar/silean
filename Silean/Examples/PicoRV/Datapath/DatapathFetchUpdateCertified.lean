import Silean.Examples.PicoRV.Datapath.DatapathFetchUpdate
import Silean.Examples.PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Add.Add
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Modules.VectorLayout.VectorLayoutCertified
import Silean.Primitives.And

namespace Silean.Examples.PicoRV.Datapath.FetchUpdate

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  four := Modules.Constant.certification (.vector 32 .bit) (wordOfNat 4),
  branchStored := Primitives.andCertified.certification,
  branchSource := Modules.Mux.certification (.vector 32 .bit),
  alignedBranch := Modules.VectorLayout.certification 32 32 clearLowLayout,
  currentPc := Modules.Mux.certification (.vector 32 .bit),
  sequentialPc := Modules.Add.certification 32,
  jalPc := Modules.Add.certification 32,
  decodedPc := Modules.Mux.certification (.vector 32 .bit),
  nextPc := Modules.Mux.certification (.vector 32 .bit),
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Modules.NamedTupleSplitter.Rule.apply,
    {.falseBit, .four} => Primitives.ConstantRule.apply,
    .branchStored => Primitives.AndRule.apply,
    .branchSource => Modules.Mux.Rule.select,
    .alignedBranch => Modules.VectorLayout.Rule.apply,
    .currentPc => Modules.Mux.Rule.select,
    {.sequentialPc, .jalPc} => Modules.Add.Rule.apply,
    .decodedPc => Modules.Mux.Rule.select,
    .nextPc => Modules.Mux.Rule.select,
    .result => Modules.NamedTupleCombiner.Rule.apply]
  state := []

theorem clearLow_layout (word : Word) :
    Modules.VectorLayout.apply clearLowLayout word = clearLowBit word := by
  funext index
  by_cases zero : index.val = 0 <;>
    simp [Modules.VectorLayout.apply, clearLowLayout, clearLowBit, zero]

def selectedCurrentPc (inputs : Inputs) (current : stateMap.Values) : Word :=
  if inputs.latched_branch && inputs.latched_store then
    clearLowBit (if inputs.latched_stalu then current .alu_out_q else current .reg_out)
  else current .reg_next_pc

def selectedNextPc (inputs : Inputs) (current : stateMap.Values) : Word :=
  let pc := selectedCurrentPc inputs current
  if inputs.decoder_trigger then
    addWords pc (if inputs.instr_jal then inputs.decoded_imm_j else wordOfNat 4)
  else pc

theorem structural_eq_fetchNextState (inputs : Inputs)
    (current updated : stateMap.Values) :
    (fun
      | .reg_pc => selectedCurrentPc inputs current
      | .reg_next_pc => selectedNextPc inputs current
      | field => updated field) = fetchNextState inputs current updated := by
  cases branch : inputs.latched_branch <;> cases store : inputs.latched_store <;>
    cases stalu : inputs.latched_stalu <;>
    cases trigger : inputs.decoder_trigger <;> cases jal : inputs.instr_jal <;>
    funext field <;> cases field <;>
    simp [fetchNextState, selectedCurrentPc, selectedNextPc, SignalMap.set,
      branch, store, stalu, trigger, jal]

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
  have fourValue := (Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 4) _ _ _).mp
    ((childMatch .four).1.1 Primitives.ConstantRule.apply)
  have branchStoredValue : (proposal.2 .branchStored).outputs .output =
      (datapathInputs.latched_branch && datapathInputs.latched_store) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .branchStored).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .latched_branch, inputField .latched_store] at equation
    exact equation
  have branchSourceValue : (proposal.2 .branchSource).outputs .result =
      (if datapathInputs.latched_stalu then current .alu_out_q else current .reg_out) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .branchSource).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .latched_stalu, currentFieldsValue] at equation
    cases stalu : datapathInputs.latched_stalu <;>
      simp [Inputs.toValues, stalu] at equation ⊢ <;> exact equation
  have alignedValue : (proposal.2 .alignedBranch).outputs .output =
      clearLowBit (if datapathInputs.latched_stalu then
        current .alu_out_q else current .reg_out) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 32 clearLowLayout
      _ _ _ _ (childMatch .alignedBranch).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [branchSourceValue, clearLow_layout] at equation
    exact equation
  have currentPcValue : (proposal.2 .currentPc).outputs .result =
      selectedCurrentPc datapathInputs current := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .currentPc).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [branchStoredValue, currentFieldsValue, alignedValue] at equation
    cases branch : datapathInputs.latched_branch <;>
      cases store : datapathInputs.latched_store <;>
      simp [selectedCurrentPc, branch, store] at equation ⊢ <;> exact equation
  have sequentialValue : (proposal.2 .sequentialPc).outputs .result =
      addWords (selectedCurrentPc datapathInputs current) (wordOfNat 4) := by
    have equation := Modules.Add.result_of_evaluatesTo 32
      _ _ _ _ (childMatch .sequentialPc).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentPcValue, fourValue, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation
  have jalValue : (proposal.2 .jalPc).outputs .result =
      addWords (selectedCurrentPc datapathInputs current)
        datapathInputs.decoded_imm_j := by
    have equation := Modules.Add.result_of_evaluatesTo 32
      _ _ _ _ (childMatch .jalPc).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentPcValue, inputField .decoded_imm_j, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation
  have decodedValue : (proposal.2 .decodedPc).outputs .result =
      addWords (selectedCurrentPc datapathInputs current)
        (if datapathInputs.instr_jal then
          datapathInputs.decoded_imm_j else wordOfNat 4) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .decodedPc).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .instr_jal, sequentialValue, jalValue] at equation
    cases jal : datapathInputs.instr_jal <;>
      simp [Inputs.toValues, jal] at equation ⊢ <;> exact equation
  have nextPcValue : (proposal.2 .nextPc).outputs .result =
      selectedNextPc datapathInputs current := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .nextPc).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .decoder_trigger, currentPcValue, decodedValue] at equation
    cases trigger : datapathInputs.decoder_trigger <;>
      simp [selectedNextPc, Inputs.toValues, trigger] at equation ⊢ <;>
      exact equation

  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result = fetchNextState datapathInputs current updated := by
    rw [← structural_eq_fetchNextState]
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value]
    · exact currentPcValue
    · exact nextPcValue
    · simpa using congrFun updatedFieldsValue .reg_op1
    · simpa using congrFun updatedFieldsValue .reg_op2
    · simpa using congrFun updatedFieldsValue .reg_out
    · simpa using congrFun updatedFieldsValue .reg_sh
    · simpa using congrFun updatedFieldsValue .alu_out_q
  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack (fetchNextState datapathInputs current updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    rw [show proposal.outputs .state = (proposal.2 .result).outputs .value by
      exact satisfies.1 .state]
    simpa [StateUpdate.outputState, datapathInputs, current, updated] using resultValue
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

end Silean.Examples.PicoRV.Datapath.FetchUpdate
