import Silean.Examples.PicoRV.Alu
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.AddSub.AddSubCertified
import Silean.Modules.Mux.MuxCertified

namespace Silean.Examples.PicoRV.Alu

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

private theorem equal_eq_signalEqual (left right : Word) :
    equal left right = (SignalType.vector 32 .bit).equal left right := by
  apply Bool.eq_iff_iff.mpr
  rw [SignalType.equal_eq_true_iff]
  simp only [equal, decide_eq_true_eq]
  constructor
  · exact fun equality => (BitVector.toNat_injective 32) equality
  · exact congrArg (BitVector.toNat 32)

@[simp] private theorem evaluateOperation_bif (select : Bool)
    (whenTrue whenFalse : Operation) (comparison : Bool)
    (reg_op1 reg_op2 : Word) :
    evaluateOperation (bif select then whenTrue else whenFalse)
        comparison reg_op1 reg_op2 =
      bif select then evaluateOperation whenTrue comparison reg_op1 reg_op2
      else evaluateOperation whenFalse comparison reg_op1 reg_op2 := by
  cases select <;> rfl

@[simp] private theorem addSub_bif (select : Bool) (reg_op1 reg_op2 : Word) :
    (bif select then addSub true reg_op1 reg_op2
      else addSub false reg_op1 reg_op2) = addSub select reg_op1 reg_op2 := by
  cases select <;> rfl

private def selectedAluOut (inputs : ports.inputs.Values) : Word :=
  bif inputs .is_lui_auipc_jal_jalr_addi_add_sub then
    addSub (inputs .instr_sub || inputs .is_compare)
      (inputs .reg_op1) (inputs .reg_op2)
  else bif inputs .is_compare then wordOfBool (comparisonOutput (valuesOf inputs))
  else bif (inputs .instr_xori || inputs .instr_xor) then
    bitwiseXor (inputs .reg_op1) (inputs .reg_op2)
  else bif (inputs .instr_ori || inputs .instr_or) then
    bitwiseOr (inputs .reg_op1) (inputs .reg_op2)
  else bif (inputs .instr_andi || inputs .instr_and) then
    bitwiseAnd (inputs .reg_op1) (inputs .reg_op2)
  else wordOfNat 0

private theorem aluOut_valuesOf (inputs : ports.inputs.Values) :
    aluOut (valuesOf inputs) = selectedAluOut inputs := by
  simp only [aluOut, evaluate, selectedOperation, valuesOf, evaluateOperation_bif]
  simp only [evaluateOperation, addSub_bif]
  rfl

private theorem wordType_bitwiseXor (left right : Word) :
    (SignalType.vector 32 .bit).bitwiseXor left right = bitwiseXor left right := by
  funext index
  simp only [SignalType.bitwiseXor, bitwiseXor]
  cases left index <;> cases right index <;> rfl

module_child_certifications childContracts for body where
  leftSplit := wordSplitter.certified.certification,
  rightSplit := wordSplitter.certified.certification,
  subtractMode := Primitives.orCertified.certification,
  addSub := Modules.AddSub.certification 32,
  equality := Modules.Equality.certification wordType,
  bitwiseXor := Modules.BitwiseXor.certification wordType,
  bitwiseOr := Modules.BitwiseOr.certification wordType,
  bitwiseAnd := Modules.BitwiseAnd.certification wordType,
  zeroBit := Modules.Constant.certification .bit zeroBitValue,
  zeroWord := Modules.Constant.certification wordType zeroWordValue,
  unsignedLess := Primitives.notCertified.certification,
  signDifference := Primitives.xorCertified.certification,
  signedLess := Modules.Mux.certification .bit,
  notEqual := Primitives.notCertified.certification,
  notSignedLess := Primitives.notCertified.certification,
  notUnsignedLess := Primitives.notCertified.certification,
  selectUnsignedLess := Modules.Mux.certification .bit,
  selectSignedLess := Modules.Mux.certification .bit,
  selectUnsignedGreaterEqual := Modules.Mux.certification .bit,
  selectSignedGreaterEqual := Modules.Mux.certification .bit,
  selectNotEqual := Modules.Mux.certification .bit,
  selectEqual := Modules.Mux.certification .bit,
  comparisonWord := wordCombiner.certified.certification,
  xorSelected := Primitives.orCertified.certification,
  orSelected := Primitives.orCertified.certification,
  andSelected := Primitives.orCertified.certification,
  selectAnd := Modules.Mux.certification wordType,
  selectOr := Modules.Mux.certification wordType,
  selectXor := Modules.Mux.certification wordType,
  selectComparison := Modules.Mux.certification wordType,
  selectArithmetic := Modules.Mux.certification wordType

/-! ## Cycle certification -/

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [.leftSplit => Composition.SignalComponentRule.apply,
        .rightSplit => Composition.SignalComponentRule.apply,
        .subtractMode => Primitives.OrRule.apply,
        .addSub => Modules.AddSub.Rule.apply,
        .equality => Modules.Equality.Rule.apply,
        .bitwiseXor => Modules.BitwiseXor.Rule.apply,
        .bitwiseOr => Modules.BitwiseOr.Rule.apply,
        .bitwiseAnd => Modules.BitwiseAnd.Rule.apply,
        .zeroBit => Primitives.ConstantRule.apply,
        .zeroWord => Primitives.ConstantRule.apply,
        .unsignedLess => Primitives.NotRule.apply,
        .signDifference => Primitives.XorRule.apply,
        .signedLess => Modules.Mux.Rule.select,
        .notEqual => Primitives.NotRule.apply,
        .notSignedLess => Primitives.NotRule.apply,
        .notUnsignedLess => Primitives.NotRule.apply,
        .selectUnsignedLess => Modules.Mux.Rule.select,
        .selectSignedLess => Modules.Mux.Rule.select,
        .selectUnsignedGreaterEqual => Modules.Mux.Rule.select,
        .selectSignedGreaterEqual => Modules.Mux.Rule.select,
        .selectNotEqual => Modules.Mux.Rule.select,
        .selectEqual => Modules.Mux.Rule.select,
        .comparisonWord => Composition.SignalComponentRule.apply,
        .xorSelected => Primitives.OrRule.apply,
        .orSelected => Primitives.OrRule.apply,
        .andSelected => Primitives.OrRule.apply,
        .selectAnd => Modules.Mux.Rule.select,
        .selectOr => Modules.Mux.Rule.select,
        .selectXor => Modules.Mux.Rule.select,
        .selectComparison => Modules.Mux.Rule.select,
        .selectArithmetic => Modules.Mux.Rule.select]
  state := []

section LayerCertification

variable (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
  body childContracts)

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies
  have leftSplitEquation :=
    (wordSplitter.outputRule_holds_iff _ _ _).mp ((childMatch .leftSplit).1.1 .apply)
  have rightSplitEquation :=
    (wordSplitter.outputRule_holds_iff _ _ _).mp ((childMatch .rightSplit).1.1 .apply)
  have leftSign : (proposal.2 .leftSplit).outputs (Fin.last 31) = inputs .reg_op1 31 := by
    have equation := congrFun leftSplitEquation (Fin.last 31)
    simpa [ProposedValues.childInputs_apply, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput,
      Composition.SignalSplitter.outputValues, wordSplitter, SignalSource.value] using equation
  have rightSign : (proposal.2 .rightSplit).outputs (Fin.last 31) = inputs .reg_op2 31 := by
    have equation := congrFun rightSplitEquation (Fin.last 31)
    simpa [ProposedValues.childInputs_apply, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput,
      Composition.SignalSplitter.outputValues, wordSplitter, SignalSource.value] using equation
  have subtractModeValue : (proposal.2 .subtractMode).outputs .output =
      (inputs .instr_sub || inputs .is_compare) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .subtractMode).1.1 .apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  have addSubResult : (proposal.2 .addSub).outputs .result =
      (Modules.AddSub.addSubBits 32 (inputs .reg_op1) (inputs .reg_op2)
        (inputs .instr_sub || inputs .is_compare)).1 := by
    have equation := Modules.AddSub.result_of_evaluatesTo 32 _ _ _ _ (childMatch .addSub).1
    simpa [ProposedValues.childInputs_apply, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value,
      subtractModeValue] using equation
  have addSubCarry : (proposal.2 .addSub).outputs .carryOut =
      (Modules.AddSub.addSubBits 32 (inputs .reg_op1) (inputs .reg_op2)
        (inputs .instr_sub || inputs .is_compare)).2 := by
    have equation := Modules.AddSub.carry_of_evaluatesTo 32 _ _ _ _ (childMatch .addSub).1
    simpa [ProposedValues.childInputs_apply, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value,
      subtractModeValue] using equation
  child_contract_fact equalityValue : (proposal.2 .equality).outputs .result =
      wordType.equal (inputs .reg_op1) (inputs .reg_op2) from
      (childMatch .equality).1 using
      Modules.Equality.result_of_evaluatesTo wordType _ _ _ _ unfolding body, wiring, context
  child_contract_fact bitwiseXorValue : (proposal.2 .bitwiseXor).outputs .result =
      wordType.bitwiseXor (inputs .reg_op1) (inputs .reg_op2) from
      (childMatch .bitwiseXor).1 using
      Modules.BitwiseXor.result_of_evaluatesTo wordType _ _ _ _ unfolding body, wiring, context
  child_contract_fact bitwiseOrValue : (proposal.2 .bitwiseOr).outputs .result =
      wordType.bitwiseOr (inputs .reg_op1) (inputs .reg_op2) from
      (childMatch .bitwiseOr).1 using
      Modules.BitwiseOr.result_of_evaluatesTo wordType _ _ _ _ unfolding body, wiring, context
  child_contract_fact bitwiseAndValue : (proposal.2 .bitwiseAnd).outputs .result =
      wordType.bitwiseAnd (inputs .reg_op1) (inputs .reg_op2) from
      (childMatch .bitwiseAnd).1 using
      Modules.BitwiseAnd.result_of_evaluatesTo wordType _ _ _ _ unfolding body, wiring, context
  have zeroBitValueEquation : (proposal.2 .zeroBit).outputs .output = false := by
    have equation := Modules.Constant.output_of_evaluatesTo .bit zeroBitValue _ _ _ _
      (childMatch .zeroBit).1
    simpa [zeroBitValue] using equation
  have zeroWordValueEquation : (proposal.2 .zeroWord).outputs .output = wordOfNat 0 := by
    have equation := Modules.Constant.output_of_evaluatesTo wordType zeroWordValue _ _ _ _
      (childMatch .zeroWord).1
    simpa [zeroWordValue] using equation
  have unsignedLessValue : (proposal.2 .unsignedLess).outputs .output =
      sharedUnsignedLess (valuesOf inputs) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .unsignedLess).1.1 .apply)
    have normalized : (proposal.2 .unsignedLess).outputs .output =
        !((proposal.2 .addSub).outputs .carryOut) := by
      simpa [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    rw [normalized, addSubCarry]
    rfl
  have signDifferenceValue : (proposal.2 .signDifference).outputs .output =
      Bool.xor (inputs .reg_op1 31) (inputs .reg_op2 31) := by
    have equation := (Primitives.xorOutputRule_holds_iff _ _ _).mp
      ((childMatch .signDifference).1.1 .apply)
    have normalized : (proposal.2 .signDifference).outputs .output =
        Primitives.xorValue ((proposal.2 .leftSplit).outputs (Fin.last 31))
          ((proposal.2 .rightSplit).outputs (Fin.last 31)) := by
      simpa [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    rw [normalized, leftSign, rightSign]
    cases inputs .reg_op1 31 <;> cases inputs .reg_op2 31 <;> rfl
  have signedLessValue : (proposal.2 .signedLess).outputs .result =
      sharedSignedLess (valuesOf inputs) := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .signedLess).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    rw [equation, signDifferenceValue, unsignedLessValue, leftSign]
    cases left : inputs .reg_op1 31 <;> cases right : inputs .reg_op2 31 <;>
      simp [sharedSignedLess, valuesOf, left, right]
  have notEqualValue : (proposal.2 .notEqual).outputs .output =
      !(equal (inputs .reg_op1) (inputs .reg_op2)) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notEqual).1.1 .apply)
    have normalized : (proposal.2 .notEqual).outputs .output =
        !((proposal.2 .equality).outputs .result) := by
      simpa [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    rw [normalized, equalityValue, ← equal_eq_signalEqual]
  have notSignedLessValue : (proposal.2 .notSignedLess).outputs .output =
      !(sharedSignedLess (valuesOf inputs)) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notSignedLess).1.1 .apply)
    have normalized : (proposal.2 .notSignedLess).outputs .output =
        !((proposal.2 .signedLess).outputs .result) := by
      simpa [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    rw [normalized, signedLessValue]
  have notUnsignedLessValue : (proposal.2 .notUnsignedLess).outputs .output =
      !(sharedUnsignedLess (valuesOf inputs)) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notUnsignedLess).1.1 .apply)
    have normalized : (proposal.2 .notUnsignedLess).outputs .output =
        !((proposal.2 .unsignedLess).outputs .output) := by
      simpa [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    rw [normalized, unsignedLessValue]
  have selectUnsignedLessValue : (proposal.2 .selectUnsignedLess).outputs .result =
      bif inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf inputs) else false := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectUnsignedLess).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, zeroBitValueEquation, unsignedLessValue]
    rfl
  have selectSignedLessValue : (proposal.2 .selectSignedLess).outputs .result =
      bif inputs .is_slti_blt_slt then sharedSignedLess (valuesOf inputs)
      else bif inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf inputs) else false := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectSignedLess).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, selectUnsignedLessValue, signedLessValue]
    rfl
  have selectUnsignedGreaterEqualValue :
      (proposal.2 .selectUnsignedGreaterEqual).outputs .result =
        bif inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf inputs))
        else bif inputs .is_slti_blt_slt then sharedSignedLess (valuesOf inputs)
        else bif inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf inputs)
        else false := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectUnsignedGreaterEqual).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, selectSignedLessValue, notUnsignedLessValue]
    rfl
  have selectSignedGreaterEqualValue :
      (proposal.2 .selectSignedGreaterEqual).outputs .result =
        bif inputs .instr_bge then !(sharedSignedLess (valuesOf inputs))
        else bif inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf inputs))
        else bif inputs .is_slti_blt_slt then sharedSignedLess (valuesOf inputs)
        else bif inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf inputs)
        else false := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectSignedGreaterEqual).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, selectUnsignedGreaterEqualValue, notSignedLessValue]
    rfl
  have selectNotEqualValue : (proposal.2 .selectNotEqual).outputs .result =
      bif inputs .instr_bne then !(equal (inputs .reg_op1) (inputs .reg_op2))
      else bif inputs .instr_bge then !(sharedSignedLess (valuesOf inputs))
      else bif inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf inputs))
      else bif inputs .is_slti_blt_slt then sharedSignedLess (valuesOf inputs)
      else bif inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf inputs)
      else false := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectNotEqual).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, selectSignedGreaterEqualValue, notEqualValue]
    rfl
  have selectEqualValue : (proposal.2 .selectEqual).outputs .result =
      comparisonOutput (valuesOf inputs) := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectEqual).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, selectNotEqualValue, equalityValue, ← equal_eq_signalEqual]
    unfold comparisonOutput valuesOf
    rfl
  have comparisonWordValue : (proposal.2 .comparisonWord).outputs .value =
      wordOfBool (comparisonOutput (valuesOf inputs)) := by
    have equation := (wordCombiner.outputRule_holds_iff _ _ _).mp
      ((childMatch .comparisonWord).1.1 .apply)
    have valueEquation := congrFun equation .value
    rw [valueEquation]
    funext index
    change Fin 32 at index
    by_cases first : index = 0
    · subst index
      simp [Composition.SignalCombiner.outputValues, wordCombiner,
        ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, selectEqualValue, wordOfBool]
    · simp [Composition.SignalCombiner.outputValues, wordCombiner,
        ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, first,
        wordOfBool]
      exact zeroBitValueEquation
  have xorSelectedValue : (proposal.2 .xorSelected).outputs .output =
      (inputs .instr_xori || inputs .instr_xor) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .xorSelected).1.1 .apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  have orSelectedValue : (proposal.2 .orSelected).outputs .output =
      (inputs .instr_ori || inputs .instr_or) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .orSelected).1.1 .apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  have andSelectedValue : (proposal.2 .andSelected).outputs .output =
      (inputs .instr_andi || inputs .instr_and) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .andSelected).1.1 .apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  -- Follow the result-selection mux chain.  Intermediate expressions are
  -- inferred instead of restating the progressively larger nested `bif`.
  have selectAndValue := Modules.Mux.result_of_evaluatesTo wordType _ _ _ _
    (childMatch .selectAnd).1
  normalize_child_hyp selectAndValue unfolding body, wiring, context
  rw [andSelectedValue, zeroWordValueEquation, bitwiseAndValue] at selectAndValue
  have selectOrValue := Modules.Mux.result_of_evaluatesTo wordType _ _ _ _
    (childMatch .selectOr).1
  normalize_child_hyp selectOrValue unfolding body, wiring, context
  rw [orSelectedValue, selectAndValue, bitwiseOrValue] at selectOrValue
  have selectXorValue := Modules.Mux.result_of_evaluatesTo wordType _ _ _ _
    (childMatch .selectXor).1
  normalize_child_hyp selectXorValue unfolding body, wiring, context
  rw [xorSelectedValue, selectOrValue, bitwiseXorValue, wordType_bitwiseXor] at selectXorValue
  have selectComparisonValue := Modules.Mux.result_of_evaluatesTo wordType _ _ _ _
    (childMatch .selectComparison).1
  normalize_child_hyp selectComparisonValue unfolding body, wiring, context
  rw [selectXorValue, comparisonWordValue] at selectComparisonValue
  have selectArithmeticValue := Modules.Mux.result_of_evaluatesTo wordType _ _ _ _
    (childMatch .selectArithmetic).1
  normalize_child_hyp selectArithmeticValue unfolding body, wiring, context
  rw [selectComparisonValue, addSubResult] at selectArithmeticValue
  have aluOutBoundary : proposal.1 .alu_out =
      (proposal.2 .selectArithmetic).outputs .result := by
    simpa [body, wiring, context, EndpointContext.instanceOutput, SignalSource.value] using
      satisfies.1 .alu_out
  have aluOut0Boundary : proposal.1 .alu_out_0 =
      (proposal.2 .selectEqual).outputs .result := by
    simpa [body, wiring, context, EndpointContext.instanceOutput, SignalSource.value] using
      satisfies.1 .alu_out_0
  have addSubBehavior (subtract : Bool) :
      addSub subtract (inputs .reg_op1) (inputs .reg_op2) =
        (Modules.AddSub.addSubBits 32 (inputs .reg_op1) (inputs .reg_op2) subtract).1 := by
    apply BitVector.toNat_injective 32
    rw [Modules.AddSub.addSubBits_result_toNat]
    cases subtract <;>
      simp [addSub, wordOfNat, BitVector.toNat_ofNat]
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · change proposal.1 .alu_out = aluOut (valuesOf inputs)
      rw [aluOutBoundary, selectArithmeticValue, aluOut_valuesOf]
      rw [← addSubBehavior (inputs .instr_sub || inputs .is_compare)]
      rfl
    · change proposal.1 .alu_out_0 = aluOut0 (valuesOf inputs)
      rw [aluOut0Boundary, selectEqualValue]
      rfl
  · rfl

private theorem hasCorrespondingState
    (structuralState :
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState :=
  ⟨SignalMap.emptyValues, trivial⟩

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

/-- The ALU hierarchy and every reusable child below it have concrete structure. -/
theorem hasExactlyOneSolution (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal ∧
      ∀ other, moduleStructure.IsSolution inputs currentState other → other = proposal :=
  certified.hasExactlyOneStructuralResult inputs currentState

end Silean.Examples.PicoRV.Alu
