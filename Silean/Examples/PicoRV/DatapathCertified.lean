import Silean.Examples.PicoRV.DatapathStructure
import Silean.Examples.PicoRV.AluCertified
import Silean.Examples.PicoRV.Datapath.DatapathNextCertified
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Add.Add
import Silean.Modules.EqualsConstant.EqualsConstantCertified
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Modules.Register.Register
import Silean.Modules.VectorLayout.VectorLayoutCertified
import Silean.Primitives.And

namespace Silean.Examples.PicoRV.Datapath

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsValue := Modules.NamedTupleCombiner.certification DatapathInputs.signalMap,
  storage := Modules.Register.certification stateType,
  stateFields := Modules.NamedTupleSplitter.certification stateMap,
  alu := Alu.certification,
  next := Next.certification,
  branchActive := Primitives.andCertified.certification,
  alignedRegOut := Modules.VectorLayout.certification 32 32
    FetchUpdate.clearLowLayout,
  nextPc := Modules.Mux.certification (.vector 32 .bit),
  fetchPhase := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  falseBit := Modules.Constant.certification .bit false,
  zeroWord := Modules.Constant.certification (.vector 32 .bit) (wordOfNat 0),
  four := Modules.Constant.certification (.vector 32 .bit) (wordOfNat 4),
  linkValue := Modules.Add.certification 32,
  storeSource := Modules.Mux.certification (.vector 32 .bit),
  storedValue := Modules.Mux.certification (.vector 32 .bit),
  fetchValue := Modules.Mux.certification (.vector 32 .bit),
  writeback := Modules.Mux.certification (.vector 32 .bit)

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .registered => [
        .storage => Primitives.RegisterRule.observe,
        .stateFields => Modules.NamedTupleSplitter.Rule.apply]
    | .nextPc => [
        .storage => Primitives.RegisterRule.observe,
        .stateFields => Modules.NamedTupleSplitter.Rule.apply,
        .branchActive => Primitives.AndRule.apply,
        .alignedRegOut => Modules.VectorLayout.Rule.apply,
        .nextPc => Modules.Mux.Rule.select]
    | .comparison => [
        .storage => Primitives.RegisterRule.observe,
        .stateFields => Modules.NamedTupleSplitter.Rule.apply,
        .alu => Alu.Rule.apply]
    | .writeback => [
        .storage => Primitives.RegisterRule.observe,
        .stateFields => Modules.NamedTupleSplitter.Rule.apply,
        .fetchPhase => Modules.EqualsConstant.Rule.apply,
        {.falseBit, .zeroWord, .four} => Primitives.ConstantRule.apply,
        .linkValue => Modules.Add.Rule.apply,
        .storeSource => Modules.Mux.Rule.select,
        .storedValue => Modules.Mux.Rule.select,
        .fetchValue => Modules.Mux.Rule.select,
        .writeback => Modules.Mux.Rule.select]
  state := [
    .inputsValue => Modules.NamedTupleCombiner.Rule.apply,
    .storage => Primitives.RegisterRule.observe,
    .stateFields => Modules.NamedTupleSplitter.Rule.apply,
    .alu => Alu.Rule.apply,
    .next => Next.Rule.apply]

private theorem equalFetchState (bits : Fin 8 → Bool) :
    (SignalType.vector 8 .bit).equal bits (stateBits cpuStateFetch) =
      decide (BitVector.toNat 8 bits = cpuStateFetch) := by
  have representation : stateBits cpuStateFetch =
      BitVector.ofNat 8 cpuStateFetch := by rfl
  rw [representation]
  apply Bool.eq_iff_iff.mpr
  rw [SignalType.equal_eq_true_iff]
  simp only [decide_eq_true_eq]
  constructor
  · intro equal
    rw [equal, BitVector.toNat_ofNat, BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt (by decide : cpuStateFetch < 2 ^ 8)]
  · intro equal
    apply BitVector.toNat_injective 8
    rw [equal, BitVector.toNat_ofNat, BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt (by decide : cpuStateFetch < 2 ^ 8)]

section LayerCertification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

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
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies

  have statelessMatch (child : Instance)
      [Subsingleton (childContracts child).state.Values]
      (state : (childContracts child).state.Values) :=
    childSolutionMatchesContract_of_subsingletonState layerChildren inputs
      structuralState proposal satisfies child state
  have inputsValueMatch := statelessMatch .inputsValue SignalMap.emptyValues
  have stateFieldsMatch := statelessMatch .stateFields SignalMap.emptyValues
  have aluMatch := statelessMatch .alu SignalMap.emptyValues
  have nextMatch := statelessMatch .next SignalMap.emptyValues
  have branchMatch :=
    letI : Subsingleton (childContracts .branchActive).state.Values := by
      change Subsingleton emptySignalMap.Values
      infer_instance
    statelessMatch .branchActive SignalMap.emptyValues
  have alignedMatch := statelessMatch .alignedRegOut SignalMap.emptyValues
  have nextPcMatch := statelessMatch .nextPc SignalMap.emptyValues
  have fetchPhaseMatch := statelessMatch .fetchPhase SignalMap.emptyValues
  have falseMatch := statelessMatch .falseBit SignalMap.emptyValues
  have zeroMatch := statelessMatch .zeroWord SignalMap.emptyValues
  have fourMatch := statelessMatch .four SignalMap.emptyValues
  have linkMatch := statelessMatch .linkValue SignalMap.emptyValues
  have storeSourceMatch := statelessMatch .storeSource SignalMap.emptyValues
  have storedValueMatch := statelessMatch .storedValue SignalMap.emptyValues
  have fetchValueMatch := statelessMatch .fetchValue SignalMap.emptyValues
  have writebackMatch := statelessMatch .writeback SignalMap.emptyValues
  have storageMatch := childSolutionMatchesContract layerChildren inputs
    structuralState proposal satisfies .storage
    (fun | .stored => stateMap.pack contractState) corresponds

  let datapathInputs := inputsOfValues inputs
  have inputsValueInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .inputsValue = datapathInputs.toValues := by
    funext field
    cases field <;>
      simp [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, SignalSource.value, Inputs.toValues,
        datapathInputs, inputsOfValues]
  have inputsValueValue : (proposal.2 .inputsValue).outputs .value =
      datapathInputs.pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
      (inputsValueMatch.1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [inputsValueInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl
  have storageOutputValue : (proposal.2 .storage).outputs .output =
      stateMap.pack contractState := by
    exact (Modules.Register.outputRule_holds_iff stateType _ _ _).mp
      (storageMatch.1.1 Primitives.RegisterRule.observe)
  have stateFieldsValue : (proposal.2 .stateFields).outputs = contractState := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      (stateFieldsMatch.1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storageOutputValue] at equation
    simpa [ProofSupport.splitValue_eq_unpack] using equation

  have aluHeld := (Alu.outputRule_holds_iff _ _ _).mp
    (aluMatch.1.1 Alu.Rule.apply)
  have aluChildInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .alu = (fun
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
    cases input <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, EndpointContext.moduleInput,
        SignalSource.value]
    · exact congrFun stateFieldsValue .reg_op1
    · exact congrFun stateFieldsValue .reg_op2
  rw [aluChildInputs] at aluHeld
  have aluWordValue : (proposal.2 .alu).outputs .alu_out =
      aluResult datapathInputs contractState := by
    simpa [aluResult, aluInputs, datapathInputs, inputsOfValues,
      Alu.aluOut, Alu.valuesOf] using aluHeld.1
  have aluComparisonValue : (proposal.2 .alu).outputs .alu_out_0 =
      aluComparison datapathInputs contractState := by
    simpa [aluComparison, aluInputs, datapathInputs, inputsOfValues,
      Alu.aluOut0, Alu.valuesOf] using aluHeld.2

  have nextValue : (proposal.2 .next).outputs .state =
      stateMap.pack (nextState datapathInputs contractState) := by
    have equation := (Next.outputRule_holds_iff _ _ _).mp
      (nextMatch.1.1 Next.Rule.apply)
    have nextInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .next = (fun
          | .inputs => datapathInputs.pack
          | .current => stateMap.pack contractState
          | .alu_out => aluResult datapathInputs contractState) := by
      funext input
      cases input
      · simpa only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using inputsValueValue
      · change (proposal.2 .storage).outputs .output =
          stateMap.pack contractState
        exact storageOutputValue
      · simpa only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using aluWordValue
    rw [nextInputs] at equation
    simpa [Next.outputState, nextState, datapathInputs] using equation

  have branchValue : (proposal.2 .branchActive).outputs .output =
      (datapathInputs.latched_store && datapathInputs.latched_branch) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (branchMatch.1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [datapathInputs, inputsOfValues] using equation
  have alignedValue : (proposal.2 .alignedRegOut).outputs .output =
      clearLowBit (contractState .reg_out) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 32
      FetchUpdate.clearLowLayout _ _ _ _ alignedMatch.1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue, FetchUpdate.clearLow_layout] at equation
    exact equation
  have nextPcValue : (proposal.2 .nextPc).outputs .result =
      nextPcOutput datapathInputs contractState := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ nextPcMatch.1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [branchValue, stateFieldsValue, alignedValue] at equation
    cases store : datapathInputs.latched_store <;>
      cases branch : datapathInputs.latched_branch <;>
      simp [nextPcOutput, nextPcFrom, store, branch] at equation ⊢ <;>
      exact equation

  have fetchPhaseValue : (proposal.2 .fetchPhase).outputs .result =
      decide (stateNumber datapathInputs = cpuStateFetch) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
      (fetchPhaseMatch.1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [equalFetchState] at equation
    simpa [stateNumber, datapathInputs, inputsOfValues] using equation
  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    (falseMatch.1.1 Primitives.ConstantRule.apply)
  have zeroValue := (Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 0) _ _ _).mp
    (zeroMatch.1.1 Primitives.ConstantRule.apply)
  have fourValue := (Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 4) _ _ _).mp
    (fourMatch.1.1 Primitives.ConstantRule.apply)
  have linkValue : (proposal.2 .linkValue).outputs .result =
      addWords (contractState .reg_pc) (wordOfNat 4) := by
    have equation := Modules.Add.result_of_evaluatesTo 32 _ _ _ _ linkMatch.1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue, fourValue, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation
  have storeSourceValue : (proposal.2 .storeSource).outputs .result =
      (if datapathInputs.latched_stalu then contractState .alu_out_q
      else contractState .reg_out) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ storeSourceMatch.1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue] at equation
    rw [show inputs .latched_stalu = datapathInputs.latched_stalu by rfl] at equation
    cases stalu : datapathInputs.latched_stalu <;>
      simp [stalu] at equation ⊢ <;> exact equation
  have storedValue : (proposal.2 .storedValue).outputs .result =
      (if datapathInputs.latched_store then
        (if datapathInputs.latched_stalu then contractState .alu_out_q
        else contractState .reg_out)
      else wordOfNat 0) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ storedValueMatch.1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storeSourceValue, zeroValue] at equation
    rw [show inputs .latched_store = datapathInputs.latched_store by rfl] at equation
    cases store : datapathInputs.latched_store <;>
      simp [store] at equation ⊢ <;> exact equation
  have fetchValue : (proposal.2 .fetchValue).outputs .result =
      (if datapathInputs.latched_branch then
        addWords (contractState .reg_pc) (wordOfNat 4)
      else if datapathInputs.latched_store then
        (if datapathInputs.latched_stalu then contractState .alu_out_q
        else contractState .reg_out)
      else wordOfNat 0) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ fetchValueMatch.1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [linkValue, storedValue] at equation
    rw [show inputs .latched_branch = datapathInputs.latched_branch by rfl] at equation
    cases branch : datapathInputs.latched_branch <;>
      simp [branch] at equation ⊢ <;> exact equation
  have writebackValue : (proposal.2 .writeback).outputs .result =
      writebackData datapathInputs contractState := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ writebackMatch.1
    normalize_child_hyp equation unfolding body, wiring, context
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
      cases rule
      · rw [registeredRule_holds_iff]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [show proposal.outputs .reg_pc =
              (proposal.2 .stateFields).outputs .reg_pc by exact satisfies.1 .reg_pc]
          exact congrFun stateFieldsValue .reg_pc
        · rw [show proposal.outputs .reg_op1 =
              (proposal.2 .stateFields).outputs .reg_op1 by exact satisfies.1 .reg_op1]
          exact congrFun stateFieldsValue .reg_op1
        · rw [show proposal.outputs .reg_op2 =
              (proposal.2 .stateFields).outputs .reg_op2 by exact satisfies.1 .reg_op2]
          exact congrFun stateFieldsValue .reg_op2
        · rw [show proposal.outputs .reg_sh =
              (proposal.2 .stateFields).outputs .reg_sh by exact satisfies.1 .reg_sh]
          exact congrFun stateFieldsValue .reg_sh
      · rw [nextPcRule_holds_iff]
        rw [show proposal.outputs .next_pc =
            (proposal.2 .nextPc).outputs .result by exact satisfies.1 .next_pc]
        simpa [nextPcOutput, datapathInputs, inputsOfValues] using nextPcValue
      · rw [comparisonRule_holds_iff]
        rw [show proposal.outputs .alu_out_0 =
            (proposal.2 .alu).outputs .alu_out_0 by exact satisfies.1 .alu_out_0]
        simpa [datapathInputs] using aluComparisonValue
      · rw [writebackRule_holds_iff]
        rw [show proposal.outputs .cpuregs_wrdata =
            (proposal.2 .writeback).outputs .result by
              exact satisfies.1 .cpuregs_wrdata]
        simpa [datapathInputs] using writebackValue
    · rfl
  · change (layerChildren .storage).certification.stateCorresponds
      (fun | .stored => stateMap.pack nextContractState)
      (proposal.2 .storage).nextState
    rw [show (fun _ => stateMap.pack nextContractState) =
        (childContracts .storage).stateRule.apply
          (ProposedValues.childInputs body
            (fun child => (layerChildren child).moduleStructure)
            inputs proposal.2 .storage)
          (fun _ => stateMap.pack contractState) by
      funext storageState
      cases storageState
      change stateMap.pack (nextState datapathInputs contractState) =
        (proposal.2 .next).outputs .state
      exact nextValue.symm]
    exact storageMatch.2

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

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Datapath
