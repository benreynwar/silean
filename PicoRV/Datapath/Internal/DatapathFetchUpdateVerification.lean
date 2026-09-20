import PicoRV.Datapath.DatapathFetchUpdate
import PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Add.AddDerived
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.VectorLayout.VectorLayoutTheorems
import Silean.Primitives.And

namespace PicoRV.Datapath.FetchUpdate

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Silean.Modules.Constant.certification .bit false,
  four := Silean.Modules.Constant.certification (.vector 32 .bit) (wordOfNat 4),
  branchStored := Silean.Primitives.andCertified.certification,
  branchSource := Silean.Modules.Mux.certification (.vector 32 .bit),
  alignedBranch := Silean.Modules.VectorLayout.certification 32 32 clearLowLayout,
  currentPc := Silean.Modules.Mux.certification (.vector 32 .bit),
  sequentialPc := Silean.Modules.Add.certification 32,
  jalPc := Silean.Modules.Add.certification 32,
  decodedPc := Silean.Modules.Mux.certification (.vector 32 .bit),
  nextPc := Silean.Modules.Mux.certification (.vector 32 .bit),
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Silean.Modules.NamedTupleSplitter.Rule.apply,
    {.falseBit, .four} => Silean.Primitives.ConstantRule.apply,
    .branchStored => Silean.Primitives.AndRule.apply,
    .branchSource => Silean.Modules.Mux.Rule.select,
    .alignedBranch => Silean.Modules.VectorLayout.Rule.apply,
    .currentPc => Silean.Modules.Mux.Rule.select,
    {.sequentialPc, .jalPc} => Silean.Modules.Add.Rule.apply,
    .decodedPc => Silean.Modules.Mux.Rule.select,
    .nextPc => Silean.Modules.Mux.Rule.select,
    .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
  state := []

theorem clearLow_layout (word : Word) :
    Silean.Modules.VectorLayout.apply clearLowLayout word = clearLowBit word := by
  funext index
  by_cases zero : index.val = 0 <;>
    simp [Silean.Modules.VectorLayout.apply, clearLowLayout, clearLowBit, zero]

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
    simp [fetchNextState, selectedCurrentPc, selectedNextPc, Silean.SignalMap.set,
      branch, store, stalu, trigger, jal]

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
    change hierStep.childOutputs .inputsFields =
      Silean.Modules.NamedTupleSplitter.splitValue DatapathInputs.signalMap
        (hierStep.inputs .inputs) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .currentFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .current) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .updatedFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .updated) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have inputField (field : DatapathInputs.Field) :
      hierStep.childOutputs .inputsFields field = datapathInputs.toValues field := by
    exact (congrFun inputsFieldsValue field).trans
      (congrFun (Inputs.toValues_unpack _).symm field)
  have falseValue := (Silean.Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Silean.Primitives.ConstantRule.apply)
  have fourValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 4) _ _ _).mp
    ((childMatch .four).ruleHolds Silean.Primitives.ConstantRule.apply)
  have branchStoredValue : hierStep.childOutputs .branchStored .output =
      (datapathInputs.latched_branch && datapathInputs.latched_store) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .branchStored).ruleHolds Silean.Primitives.AndRule.apply)
    change hierStep.childOutputs .branchStored .output =
      (hierStep.childOutputs .inputsFields .latched_branch &&
        hierStep.childOutputs .inputsFields .latched_store) at equation
    rw [inputField .latched_branch, inputField .latched_store] at equation
    exact equation
  have branchSourceValue : hierStep.childOutputs .branchSource .result =
      (if datapathInputs.latched_stalu then current .alu_out_q else current .reg_out) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .branchSource).allowed
    change hierStep.childOutputs .branchSource .result =
      bif hierStep.childOutputs .inputsFields .latched_stalu
      then hierStep.childOutputs .currentFields .alu_out_q
      else hierStep.childOutputs .currentFields .reg_out at equation
    rw [inputField .latched_stalu, currentFieldsValue] at equation
    cases stalu : datapathInputs.latched_stalu <;>
      simp [Inputs.toValues, stalu] at equation ⊢ <;> exact equation
  have alignedValue : hierStep.childOutputs .alignedBranch .output =
      clearLowBit (if datapathInputs.latched_stalu then
        current .alu_out_q else current .reg_out) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 32 clearLowLayout
      (childMatch .alignedBranch).allowed
    change hierStep.childOutputs .alignedBranch .output =
      Silean.Modules.VectorLayout.apply clearLowLayout
        (hierStep.childOutputs .branchSource .result) at equation
    rw [branchSourceValue, clearLow_layout] at equation
    exact equation
  have currentPcValue : hierStep.childOutputs .currentPc .result =
      selectedCurrentPc datapathInputs current := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .currentPc).allowed
    change hierStep.childOutputs .currentPc .result =
      bif hierStep.childOutputs .branchStored .output
      then hierStep.childOutputs .alignedBranch .output
      else hierStep.childOutputs .currentFields .reg_next_pc at equation
    rw [branchStoredValue, currentFieldsValue, alignedValue] at equation
    cases branch : datapathInputs.latched_branch <;>
      cases store : datapathInputs.latched_store <;>
      simp [selectedCurrentPc, branch, store] at equation ⊢ <;> exact equation
  have sequentialValue : hierStep.childOutputs .sequentialPc .result =
      addWords (selectedCurrentPc datapathInputs current) (wordOfNat 4) := by
    have equation := Silean.Modules.Add.cycleContract.result 32
      (childMatch .sequentialPc).allowed
    change hierStep.childOutputs .sequentialPc .result =
      (Silean.Modules.Add.addBits 32 (hierStep.childOutputs .currentPc .result)
        (hierStep.childOutputs .four .output)
        (hierStep.childOutputs .falseBit .output)).1 at equation
    rw [currentPcValue, fourValue, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation
  have jalValue : hierStep.childOutputs .jalPc .result =
      addWords (selectedCurrentPc datapathInputs current)
        datapathInputs.decoded_imm_j := by
    have equation := Silean.Modules.Add.cycleContract.result 32
      (childMatch .jalPc).allowed
    change hierStep.childOutputs .jalPc .result =
      (Silean.Modules.Add.addBits 32 (hierStep.childOutputs .currentPc .result)
        (hierStep.childOutputs .inputsFields .decoded_imm_j)
        (hierStep.childOutputs .falseBit .output)).1 at equation
    rw [currentPcValue, inputField .decoded_imm_j, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation
  have decodedValue : hierStep.childOutputs .decodedPc .result =
      addWords (selectedCurrentPc datapathInputs current)
        (if datapathInputs.instr_jal then
          datapathInputs.decoded_imm_j else wordOfNat 4) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .decodedPc).allowed
    change hierStep.childOutputs .decodedPc .result =
      bif hierStep.childOutputs .inputsFields .instr_jal
      then hierStep.childOutputs .jalPc .result
      else hierStep.childOutputs .sequentialPc .result at equation
    rw [inputField .instr_jal, sequentialValue, jalValue] at equation
    cases jal : datapathInputs.instr_jal <;>
      simp [Inputs.toValues, jal] at equation ⊢ <;> exact equation
  have nextPcValue : hierStep.childOutputs .nextPc .result =
      selectedNextPc datapathInputs current := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .nextPc).allowed
    change hierStep.childOutputs .nextPc .result =
      bif hierStep.childOutputs .inputsFields .decoder_trigger
      then hierStep.childOutputs .decodedPc .result
      else hierStep.childOutputs .currentPc .result at equation
    rw [inputField .decoder_trigger, currentPcValue, decodedValue] at equation
    cases trigger : datapathInputs.decoder_trigger <;>
      simp [selectedNextPc, Inputs.toValues, trigger] at equation ⊢ <;>
      exact equation

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result = fetchNextState datapathInputs current updated := by
    rw [← structural_eq_fetchNextState]
    funext field
    cases field
    · change hierStep.childOutputs .currentPc .result = _; exact currentPcValue
    · change hierStep.childOutputs .nextPc .result = _; exact nextPcValue
    · change hierStep.childOutputs .updatedFields .reg_op1 = _
      exact congrFun updatedFieldsValue .reg_op1
    · change hierStep.childOutputs .updatedFields .reg_op2 = _
      exact congrFun updatedFieldsValue .reg_op2
    · change hierStep.childOutputs .updatedFields .reg_out = _
      exact congrFun updatedFieldsValue .reg_out
    · change hierStep.childOutputs .updatedFields .reg_sh = _
      exact congrFun updatedFieldsValue .reg_sh
    · change hierStep.childOutputs .updatedFields .alu_out_q = _
      exact congrFun updatedFieldsValue .alu_out_q
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (fetchNextState datapathInputs current updated) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .result .value by
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
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Datapath.FetchUpdate
