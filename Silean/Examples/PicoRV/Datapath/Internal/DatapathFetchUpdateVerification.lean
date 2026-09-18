import Silean.Examples.PicoRV.Datapath.DatapathFetchUpdate
import Silean.Examples.PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Add.AddTheorems
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.VectorLayout.VectorLayoutTheorems
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
    Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
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
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .inputsFields =
      Modules.NamedTupleSplitter.splitValue DatapathInputs.signalMap
        (hierStep.inputs .inputs) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .currentFields =
      Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .current) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .updatedFields =
      Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .updated) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]
  have inputField (field : DatapathInputs.Field) :
      hierStep.childOutputs .inputsFields field = datapathInputs.toValues field := by
    rw [inputsFieldsValue]
    cases field <;> rfl
  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Primitives.ConstantRule.apply)
  have fourValue := (Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 4) _ _ _).mp
    ((childMatch .four).ruleHolds Primitives.ConstantRule.apply)
  have branchStoredValue : hierStep.childOutputs .branchStored .output =
      (datapathInputs.latched_branch && datapathInputs.latched_store) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .branchStored).ruleHolds Primitives.AndRule.apply)
    change hierStep.childOutputs .branchStored .output =
      (hierStep.childOutputs .inputsFields .latched_branch &&
        hierStep.childOutputs .inputsFields .latched_store) at equation
    rw [inputField .latched_branch, inputField .latched_store] at equation
    exact equation
  have branchSourceValue : hierStep.childOutputs .branchSource .result =
      (if datapathInputs.latched_stalu then current .alu_out_q else current .reg_out) := by
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit)
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
    have equation := Modules.VectorLayout.output_of_allowed 32 32 clearLowLayout
      (childMatch .alignedBranch).allowed
    change hierStep.childOutputs .alignedBranch .output =
      Modules.VectorLayout.apply clearLowLayout
        (hierStep.childOutputs .branchSource .result) at equation
    rw [branchSourceValue, clearLow_layout] at equation
    exact equation
  have currentPcValue : hierStep.childOutputs .currentPc .result =
      selectedCurrentPc datapathInputs current := by
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit)
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
    have equation :=
      (Modules.Add.Behavior.of_allowed 32
        (childMatch .sequentialPc).allowed).result
    change hierStep.childOutputs .sequentialPc .result =
      (Modules.Add.addBits 32 (hierStep.childOutputs .currentPc .result)
        (hierStep.childOutputs .four .output)
        (hierStep.childOutputs .falseBit .output)).1 at equation
    rw [currentPcValue, fourValue, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation
  have jalValue : hierStep.childOutputs .jalPc .result =
      addWords (selectedCurrentPc datapathInputs current)
        datapathInputs.decoded_imm_j := by
    have equation :=
      (Modules.Add.Behavior.of_allowed 32 (childMatch .jalPc).allowed).result
    change hierStep.childOutputs .jalPc .result =
      (Modules.Add.addBits 32 (hierStep.childOutputs .currentPc .result)
        (hierStep.childOutputs .inputsFields .decoded_imm_j)
        (hierStep.childOutputs .falseBit .output)).1 at equation
    rw [currentPcValue, inputField .decoded_imm_j, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation
  have decodedValue : hierStep.childOutputs .decodedPc .result =
      addWords (selectedCurrentPc datapathInputs current)
        (if datapathInputs.instr_jal then
          datapathInputs.decoded_imm_j else wordOfNat 4) := by
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit)
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
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit)
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
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end Silean.Examples.PicoRV.Datapath.FetchUpdate
