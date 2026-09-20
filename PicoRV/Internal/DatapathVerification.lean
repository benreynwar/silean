import PicoRV.Internal.DatapathStructure
import PicoRV.AluTheorems
import PicoRV.Datapath.Internal.DatapathNextVerification
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Add.AddDerived
import Silean.Modules.EqualsConstant.EqualsConstantTheorems
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.Register.RegisterDerived
import Silean.Modules.VectorLayout.VectorLayoutTheorems
import Silean.Primitives.And

namespace PicoRV.Datapath

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsValue := Silean.Modules.NamedTupleCombiner.certification DatapathInputs.signalMap,
  storage := Silean.Modules.Register.certification stateType,
  stateFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  alu := Alu.certification,
  next := Next.certification,
  branchActive := Silean.Primitives.andCertified.certification,
  alignedRegOut := Silean.Modules.VectorLayout.certification 32 32
    FetchUpdate.clearLowLayout,
  nextPc := Silean.Modules.Mux.certification (.vector 32 .bit),
  fetchPhase := Silean.Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  falseBit := Silean.Modules.Constant.certification .bit false,
  zeroWord := Silean.Modules.Constant.certification (.vector 32 .bit) (wordOfNat 0),
  four := Silean.Modules.Constant.certification (.vector 32 .bit) (wordOfNat 4),
  linkValue := Silean.Modules.Add.certification 32,
  storeSource := Silean.Modules.Mux.certification (.vector 32 .bit),
  storedValue := Silean.Modules.Mux.certification (.vector 32 .bit),
  fetchValue := Silean.Modules.Mux.certification (.vector 32 .bit),
  writeback := Silean.Modules.Mux.certification (.vector 32 .bit)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .registered => [
        .storage => Silean.Primitives.RegisterRule.observe,
        .stateFields => Silean.Modules.NamedTupleSplitter.Rule.apply]
    | .nextPc => [
        .storage => Silean.Primitives.RegisterRule.observe,
        .stateFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .branchActive => Silean.Primitives.AndRule.apply,
        .alignedRegOut => Silean.Modules.VectorLayout.Rule.apply,
        .nextPc => Silean.Modules.Mux.Rule.select]
    | .comparison => [
        .storage => Silean.Primitives.RegisterRule.observe,
        .stateFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .alu => Alu.Rule.apply]
    | .writeback => [
        .storage => Silean.Primitives.RegisterRule.observe,
        .stateFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .fetchPhase => Silean.Modules.EqualsConstant.Rule.apply,
        {.falseBit, .zeroWord, .four} => Silean.Primitives.ConstantRule.apply,
        .linkValue => Silean.Modules.Add.Rule.apply,
        .storeSource => Silean.Modules.Mux.Rule.select,
        .storedValue => Silean.Modules.Mux.Rule.select,
        .fetchValue => Silean.Modules.Mux.Rule.select,
        .writeback => Silean.Modules.Mux.Rule.select]
  state := [
    .inputsValue => Silean.Modules.NamedTupleCombiner.Rule.apply,
    .storage => Silean.Primitives.RegisterRule.observe,
    .stateFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
    .alu => Alu.Rule.apply,
    .next => Next.Rule.apply]

private theorem equalFetchState (bits : Fin 8 → Bool) :
    (Silean.SignalType.vector 8 .bit).equal bits (stateBits cpuStateFetch) =
      decide (Silean.BitVector.toNat 8 bits = cpuStateFetch) := by
  have representation : stateBits cpuStateFetch =
      Silean.BitVector.ofNat 8 cpuStateFetch := by rfl
  rw [representation]
  apply Bool.eq_iff_iff.mpr
  rw [Silean.SignalType.equal_eq_true_iff]
  simp only [decide_eq_true_eq]
  constructor
  · intro equal
    rw [equal, Silean.BitVector.toNat_ofNat, Silean.BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt (by decide : cpuStateFetch < 2 ^ 8)]
  · intro equal
    apply Silean.BitVector.toNat_injective 8
    rw [equal, Silean.BitVector.toNat_ofNat, Silean.BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt (by decide : cpuStateFetch < 2 ^ 8)]

section LayerCertification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

/-! The structural state belongs solely to the aggregate register. Its stored
tuple is exactly the packing of the seven named fields in the contract state. -/
private def stateCorresponds (contractState : cycleContract.state.Values)
    (structuralState : (certificationStructure layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    (fun | .stored => stateMap.pack contractState)
    (structuralState .storage)

private theorem hasCorrespondingState
    (structuralState : (certificationStructure layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState := by
  rcases (layerChildren .storage).certification.hasCorrespondingState
      (structuralState .storage) with ⟨storageState, storageCorresponds⟩
  refine ⟨stateMap.unpack (storageState .stored), ?_⟩
  change (layerChildren .storage).certification.stateCorresponds
    (fun | .stored => stateMap.pack (stateMap.unpack (storageState .stored)))
    (structuralState .storage)
  simpa using storageCorresponds

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs

  have coveredMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec
  have inputsValueMatch := coveredMatch .inputsValue
  have stateFieldsMatch := coveredMatch .stateFields
  have aluMatch := coveredMatch .alu
  have nextMatch := coveredMatch .next
  have branchMatch := coveredMatch .branchActive
  have alignedMatch := coveredMatch .alignedRegOut
  have nextPcMatch := coveredMatch .nextPc
  have fetchPhaseMatch := coveredMatch .fetchPhase
  have falseMatch := coveredMatch .falseBit
  have zeroMatch := coveredMatch .zeroWord
  have fourMatch := coveredMatch .four
  have linkMatch := coveredMatch .linkValue
  have storeSourceMatch := coveredMatch .storeSource
  have storedValueMatch := coveredMatch .storedValue
  have fetchValueMatch := coveredMatch .fetchValue
  have writebackMatch := coveredMatch .writeback
  have storageMatch := childSolutionMatchesContract layerChildren hierStep
    satisfies .storage
    (fun | .stored => stateMap.pack contractState) corresponds

  let datapathInputs := inputsOfValues inputs
  have inputsValueInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .inputsValue = datapathInputs.toValues := by
    funext field
    cases field <;> rfl
  have inputsValueValue : hierStep.childOutputs .inputsValue .value =
      datapathInputs.pack := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      (inputsValueMatch.ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [inputsValueInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl
  have storageOutputValue : hierStep.childOutputs .storage .output =
      stateMap.pack contractState := by
    exact Silean.Modules.Register.output_of_allowed storageMatch.allowed
  have stateFieldsValue : hierStep.childOutputs .stateFields = contractState := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      (stateFieldsMatch.ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [storageOutputValue] at equation
    simpa [ProofSupport.splitValue_eq_unpack] using equation

  have aluHeld := (Alu.outputRule_holds_iff _ _ _).mp
    (aluMatch.ruleHolds Alu.Rule.apply)
  have aluChildInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .alu = (fun
        | .reg_op1 => contractState .reg_op1
        | .reg_op2 => contractState .reg_op2
        | .instr_sub => inputs .instr_sub
        | .instr_beq => inputs .instr_beq
        | .instr_bne => inputs .instr_bne
        | .instr_bge => inputs .instr_bge
        | .instr_bgeu => inputs .instr_bgeu
        | .is_slti_blt_slt => inputs .is_slti_blt_slt
        | .is_sltiu_bltu_sltu => inputs .is_sltiu_bltu_sltu
        | .is_lui_auipc_jal_jalr_addi_add_sub =>
            inputs .is_lui_auipc_jal_jalr_addi_add_sub
        | .is_compare => inputs .is_compare
        | .instr_xori => inputs .instr_xori
        | .instr_xor => inputs .instr_xor
        | .instr_ori => inputs .instr_ori
        | .instr_or => inputs .instr_or
        | .instr_andi => inputs .instr_andi
        | .instr_and => inputs .instr_and) := by
    funext input
    cases input
    · change hierStep.childOutputs .stateFields .reg_op1 = _
      exact congrFun stateFieldsValue .reg_op1
    · change hierStep.childOutputs .stateFields .reg_op2 = _
      exact congrFun stateFieldsValue .reg_op2
    all_goals rfl
  rw [aluChildInputs] at aluHeld
  have aluWordValue : hierStep.childOutputs .alu .alu_out =
      aluResult datapathInputs contractState := by
    simpa [aluResult, aluInputs, datapathInputs, inputsOfValues,
      Alu.aluOut, Alu.valuesOf] using aluHeld.1
  have aluComparisonValue : hierStep.childOutputs .alu .alu_out_0 =
      aluComparison datapathInputs contractState := by
    simpa [aluComparison, aluInputs, datapathInputs, inputsOfValues,
      Alu.aluOut0, Alu.valuesOf] using aluHeld.2

  have nextValue : hierStep.childOutputs .next .state =
      stateMap.pack (nextState datapathInputs contractState) := by
    have equation := (Next.outputRule_holds_iff _ _ _).mp
      (nextMatch.ruleHolds Next.Rule.apply)
    have nextInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .next = (fun
          | .inputs => datapathInputs.pack
          | .current => stateMap.pack contractState
          | .alu_out => aluResult datapathInputs contractState) := by
      funext input
      cases input
      · change hierStep.childOutputs .inputsValue .value = _
        exact inputsValueValue
      · change hierStep.childOutputs .storage .output =
          stateMap.pack contractState
        exact storageOutputValue
      · change hierStep.childOutputs .alu .alu_out = _
        exact aluWordValue
    rw [nextInputs] at equation
    simpa [Next.outputState, nextState, datapathInputs] using equation

  have branchValue : hierStep.childOutputs .branchActive .output =
      (datapathInputs.latched_store && datapathInputs.latched_branch) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      (branchMatch.ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [datapathInputs, inputsOfValues] using equation
  have alignedValue : hierStep.childOutputs .alignedRegOut .output =
      clearLowBit (contractState .reg_out) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 32
      FetchUpdate.clearLowLayout alignedMatch.allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [stateFieldsValue, FetchUpdate.clearLow_layout] at equation
    exact equation
  have nextPcValue : hierStep.childOutputs .nextPc .result =
      nextPcOutput datapathInputs contractState := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      nextPcMatch.allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [branchValue, stateFieldsValue, alignedValue] at equation
    cases store : datapathInputs.latched_store <;>
      cases branch : datapathInputs.latched_branch <;>
      simp [nextPcOutput, nextPcFrom, store, branch] at equation ⊢ <;>
      exact equation

  have fetchPhaseValue : hierStep.childOutputs .fetchPhase .result =
      decide (stateNumber datapathInputs = cpuStateFetch) := by
    have equation := Silean.Modules.EqualsConstant.result_of_allowed
      (.vector 8 .bit) (stateBits cpuStateFetch)
      fetchPhaseMatch.allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [equalFetchState] at equation
    simpa [stateNumber, datapathInputs, inputsOfValues] using equation
  have falseValue := (Silean.Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    (falseMatch.ruleHolds Silean.Primitives.ConstantRule.apply)
  have zeroValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 0) _ _ _).mp
    (zeroMatch.ruleHolds Silean.Primitives.ConstantRule.apply)
  have fourValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 4) _ _ _).mp
    (fourMatch.ruleHolds Silean.Primitives.ConstantRule.apply)
  have linkValue : hierStep.childOutputs .linkValue .result =
      addWords (contractState .reg_pc) (wordOfNat 4) := by
    have equation := Silean.Modules.Add.cycleContract.result 32 linkMatch.1
    normalize_child_hyp equation unfolding wiring, context
    rw [stateFieldsValue, fourValue, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation
  have storeSourceValue : hierStep.childOutputs .storeSource .result =
      (if datapathInputs.latched_stalu then contractState .alu_out_q
      else contractState .reg_out) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      storeSourceMatch.allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [stateFieldsValue] at equation
    rw [show hierStep.inputs .latched_stalu =
      datapathInputs.latched_stalu by rfl] at equation
    cases stalu : datapathInputs.latched_stalu <;>
      simp [stalu] at equation ⊢ <;> exact equation
  have storedValue : hierStep.childOutputs .storedValue .result =
      (if datapathInputs.latched_store then
        (if datapathInputs.latched_stalu then contractState .alu_out_q
        else contractState .reg_out)
      else wordOfNat 0) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      storedValueMatch.allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [storeSourceValue, zeroValue] at equation
    rw [show hierStep.inputs .latched_store =
      datapathInputs.latched_store by rfl] at equation
    cases store : datapathInputs.latched_store <;>
      simp [store] at equation ⊢ <;> exact equation
  have fetchValue : hierStep.childOutputs .fetchValue .result =
      (if datapathInputs.latched_branch then
        addWords (contractState .reg_pc) (wordOfNat 4)
      else if datapathInputs.latched_store then
        (if datapathInputs.latched_stalu then contractState .alu_out_q
        else contractState .reg_out)
      else wordOfNat 0) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      fetchValueMatch.allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [linkValue, storedValue] at equation
    rw [show hierStep.inputs .latched_branch =
      datapathInputs.latched_branch by rfl] at equation
    cases branch : datapathInputs.latched_branch <;>
      simp [branch] at equation ⊢ <;> exact equation
  have writebackValue : hierStep.childOutputs .writeback .result =
      writebackData datapathInputs contractState := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      writebackMatch.allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [fetchPhaseValue, zeroValue, fetchValue] at equation
    by_cases fetch : stateNumber datapathInputs = cpuStateFetch
    · simp [writebackData, writebackFrom, fetch] at equation ⊢
      exact equation
    · simp [writebackData, writebackFrom, fetch] at equation ⊢
      exact equation

  let nextContractState := stateRule.apply inputs contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      dsimp only
      cases rule
      · rw [registeredRule_holds_iff]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [show hierStep.outputs .reg_pc =
              hierStep.childOutputs .stateFields .reg_pc by exact satisfies.1 .reg_pc]
          exact congrFun stateFieldsValue .reg_pc
        · rw [show hierStep.outputs .reg_op1 =
              hierStep.childOutputs .stateFields .reg_op1 by exact satisfies.1 .reg_op1]
          exact congrFun stateFieldsValue .reg_op1
        · rw [show hierStep.outputs .reg_op2 =
              hierStep.childOutputs .stateFields .reg_op2 by exact satisfies.1 .reg_op2]
          exact congrFun stateFieldsValue .reg_op2
        · rw [show hierStep.outputs .reg_sh =
              hierStep.childOutputs .stateFields .reg_sh by exact satisfies.1 .reg_sh]
          exact congrFun stateFieldsValue .reg_sh
      · rw [nextPcRule_holds_iff]
        rw [show hierStep.outputs .next_pc =
            hierStep.childOutputs .nextPc .result by exact satisfies.1 .next_pc]
        simpa [nextPcOutput, datapathInputs, inputsOfValues] using nextPcValue
      · rw [comparisonRule_holds_iff]
        rw [show hierStep.outputs .alu_out_0 =
            hierStep.childOutputs .alu .alu_out_0 by exact satisfies.1 .alu_out_0]
        simpa [datapathInputs] using aluComparisonValue
      · rw [writebackRule_holds_iff]
        rw [show hierStep.outputs .cpuregs_wrdata =
            hierStep.childOutputs .writeback .result by
              exact satisfies.1 .cpuregs_wrdata]
        simpa [datapathInputs] using writebackValue
    · rfl
  · change (layerChildren .storage).certification.stateCorresponds
      (fun | .stored => stateMap.pack nextContractState)
      (Silean.HierStep.nextState (layerChildren .storage).moduleStructure
        (hierStep.children .storage))
    rw [show (fun _ => stateMap.pack nextContractState) =
        (childContracts .storage).stateRule.apply
          (body.wiring.childInputValues hierStep.inputs
            hierStep.childOutputs .storage)
          (fun _ => stateMap.pack contractState) by
      funext storageState
      cases storageState
      change stateMap.pack (nextState datapathInputs contractState) =
        hierStep.childOutputs .next .state
      exact nextValue.symm]
    exact storageMatch.nextCorresponds

end LayerCertification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := hasCorrespondingState,
  implements := implements

end PicoRV.Datapath
