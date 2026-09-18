import Silean.Examples.PicoRV.Alu
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.AddSub.AddSubTheorems
import Silean.Modules.Equality.EqualityTheorems
import Silean.Modules.Mux.MuxTheorems

/-! Internal schedules and structural certification for the PicoRV ALU. -/

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

private theorem primitiveXor_eq_boolXor (left right : Bool) :
    Primitives.xorValue left right = Bool.xor left right := by
  cases left <;> cases right <;> rfl

private theorem mux_congr {α : Type} {result : α} {select select' : Bool}
    {whenTrue whenTrue' whenFalse whenFalse' : α}
    (equation : result = bif select then whenTrue else whenFalse)
    (selectEq : select = select') (whenTrueEq : whenTrue = whenTrue')
    (whenFalseEq : whenFalse = whenFalse') :
    result = bif select' then whenTrue' else whenFalse' := by
  exact equation.trans (bif_congr selectEq whenTrueEq whenFalseEq)

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
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies
  have leftSplitEquation :=
    (wordSplitter.outputRule_holds_iff _ _ _).mp ((childMatch .leftSplit).ruleHolds .apply)
  have rightSplitEquation :=
    (wordSplitter.outputRule_holds_iff _ _ _).mp ((childMatch .rightSplit).ruleHolds .apply)
  have leftSign : hierStep.childOutputs .leftSplit (Fin.last 31) = hierStep.inputs .reg_op1 31 := by
    have equation := congrFun leftSplitEquation (Fin.last 31)
    simpa [Wiring.childInputValues, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput,
      Composition.SignalSplitter.outputValues, wordSplitter, SignalSource.value] using equation
  have rightSign : hierStep.childOutputs .rightSplit (Fin.last 31) = hierStep.inputs .reg_op2 31 := by
    have equation := congrFun rightSplitEquation (Fin.last 31)
    simpa [Wiring.childInputValues, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput,
      Composition.SignalSplitter.outputValues, wordSplitter, SignalSource.value] using equation
  have subtractModeValue : hierStep.childOutputs .subtractMode .output =
      (hierStep.inputs .instr_sub || hierStep.inputs .is_compare) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .subtractMode).ruleHolds .apply)
    simpa [Wiring.childInputValues, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  have addSubResult : hierStep.childOutputs .addSub .result =
      (Modules.AddSub.addSubBits 32 (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2)
        (hierStep.inputs .instr_sub || hierStep.inputs .is_compare)).1 := by
    have equation :=
      (Modules.AddSub.Behavior.of_allowed 32 (childMatch .addSub).allowed).result
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun subtract => (Modules.AddSub.addSubBits 32
        (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) subtract).1)
      subtractModeValue)
  have addSubCarry : hierStep.childOutputs .addSub .carryOut =
      (Modules.AddSub.addSubBits 32 (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2)
        (hierStep.inputs .instr_sub || hierStep.inputs .is_compare)).2 := by
    have equation :=
      (Modules.AddSub.Behavior.of_allowed 32 (childMatch .addSub).allowed).carryOut
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun subtract => (Modules.AddSub.addSubBits 32
        (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) subtract).2)
      subtractModeValue)
  child_contract_fact equalityValue : hierStep.childOutputs .equality .result =
      wordType.equal (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) from
      (childMatch .equality).allowed using
      Modules.Equality.result_of_allowed wordType unfolding body, wiring, context
  child_contract_fact bitwiseXorValue : hierStep.childOutputs .bitwiseXor .result =
      wordType.bitwiseXor (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) from
      (childMatch .bitwiseXor).allowed using
      Modules.BitwiseXor.result_of_allowed wordType unfolding body, wiring, context
  child_contract_fact bitwiseOrValue : hierStep.childOutputs .bitwiseOr .result =
      wordType.bitwiseOr (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) from
      (childMatch .bitwiseOr).allowed using
      Modules.BitwiseOr.result_of_allowed wordType unfolding body, wiring, context
  child_contract_fact bitwiseAndValue : hierStep.childOutputs .bitwiseAnd .result =
      wordType.bitwiseAnd (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) from
      (childMatch .bitwiseAnd).allowed using
      Modules.BitwiseAnd.result_of_allowed wordType unfolding body, wiring, context
  have zeroBitValueEquation : hierStep.childOutputs .zeroBit .output = false := by
    have equation := Modules.Constant.output_of_allowed .bit zeroBitValue
      (childMatch .zeroBit).allowed
    simpa [zeroBitValue] using equation
  have zeroWordValueEquation : hierStep.childOutputs .zeroWord .output = wordOfNat 0 := by
    have equation := Modules.Constant.output_of_allowed wordType zeroWordValue
      (childMatch .zeroWord).allowed
    simpa [zeroWordValue] using equation
  have unsignedLessValue : hierStep.childOutputs .unsignedLess .output =
      sharedUnsignedLess (valuesOf hierStep.inputs) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .unsignedLess).ruleHolds .apply)
    have normalized : hierStep.childOutputs .unsignedLess .output =
        !(hierStep.childOutputs .addSub .carryOut) := by
      simpa [Wiring.childInputValues, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    exact normalized.trans (congrArg Bool.not addSubCarry)
  have signDifferenceValue : hierStep.childOutputs .signDifference .output =
      Bool.xor (hierStep.inputs .reg_op1 31) (hierStep.inputs .reg_op2 31) := by
    have equation := (Primitives.xorOutputRule_holds_iff _ _ _).mp
      ((childMatch .signDifference).ruleHolds .apply)
    have normalized : hierStep.childOutputs .signDifference .output =
        Primitives.xorValue (hierStep.childOutputs .leftSplit (Fin.last 31))
          (hierStep.childOutputs .rightSplit (Fin.last 31)) := by
      simpa [Wiring.childInputValues, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    exact (normalized.trans
      (apply₂_congr Primitives.xorValue leftSign rightSign)).trans
      (primitiveXor_eq_boolXor _ _)
  have signedLessValue : hierStep.childOutputs .signedLess .result =
      sharedSignedLess (valuesOf hierStep.inputs) := by
    have equation := Modules.Mux.result_of_allowed .bit
      (childMatch .signedLess).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    have selected := mux_congr equation signDifferenceValue leftSign unsignedLessValue
    exact selected.trans <| by
      cases left : hierStep.inputs .reg_op1 31 <;>
        cases right : hierStep.inputs .reg_op2 31 <;>
          simp [sharedSignedLess, valuesOf, left, right]
  have notEqualValue : hierStep.childOutputs .notEqual .output =
      !(equal (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2)) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notEqual).ruleHolds .apply)
    have normalized : hierStep.childOutputs .notEqual .output =
        !(hierStep.childOutputs .equality .result) := by
      simpa [Wiring.childInputValues, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    exact normalized.trans ((congrArg Bool.not equalityValue).trans
      (congrArg Bool.not (equal_eq_signalEqual _ _).symm))
  have notSignedLessValue : hierStep.childOutputs .notSignedLess .output =
      !(sharedSignedLess (valuesOf hierStep.inputs)) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notSignedLess).ruleHolds .apply)
    have normalized : hierStep.childOutputs .notSignedLess .output =
        !(hierStep.childOutputs .signedLess .result) := by
      simpa [Wiring.childInputValues, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    exact normalized.trans (congrArg Bool.not signedLessValue)
  have notUnsignedLessValue : hierStep.childOutputs .notUnsignedLess .output =
      !(sharedUnsignedLess (valuesOf hierStep.inputs)) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notUnsignedLess).ruleHolds .apply)
    have normalized : hierStep.childOutputs .notUnsignedLess .output =
        !(hierStep.childOutputs .unsignedLess .output) := by
      simpa [Wiring.childInputValues, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    exact normalized.trans (congrArg Bool.not unsignedLessValue)
  have selectUnsignedLessValue : hierStep.childOutputs .selectUnsignedLess .result =
      bif hierStep.inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf hierStep.inputs) else false := by
    have equation := Modules.Mux.result_of_allowed .bit
      (childMatch .selectUnsignedLess).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    exact mux_congr equation rfl unsignedLessValue zeroBitValueEquation
  have selectSignedLessValue : hierStep.childOutputs .selectSignedLess .result =
      bif hierStep.inputs .is_slti_blt_slt then sharedSignedLess (valuesOf hierStep.inputs)
      else bif hierStep.inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf hierStep.inputs) else false := by
    have equation := Modules.Mux.result_of_allowed .bit
      (childMatch .selectSignedLess).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    exact mux_congr equation rfl signedLessValue selectUnsignedLessValue
  have selectUnsignedGreaterEqualValue :
      hierStep.childOutputs .selectUnsignedGreaterEqual .result =
        bif hierStep.inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf hierStep.inputs))
        else bif hierStep.inputs .is_slti_blt_slt then sharedSignedLess (valuesOf hierStep.inputs)
        else bif hierStep.inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf hierStep.inputs)
        else false := by
    have equation := Modules.Mux.result_of_allowed .bit
      (childMatch .selectUnsignedGreaterEqual).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    exact mux_congr equation rfl notUnsignedLessValue selectSignedLessValue
  have selectSignedGreaterEqualValue :
      hierStep.childOutputs .selectSignedGreaterEqual .result =
        bif hierStep.inputs .instr_bge then !(sharedSignedLess (valuesOf hierStep.inputs))
        else bif hierStep.inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf hierStep.inputs))
        else bif hierStep.inputs .is_slti_blt_slt then sharedSignedLess (valuesOf hierStep.inputs)
        else bif hierStep.inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf hierStep.inputs)
        else false := by
    have equation := Modules.Mux.result_of_allowed .bit
      (childMatch .selectSignedGreaterEqual).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    exact mux_congr equation rfl notSignedLessValue
      selectUnsignedGreaterEqualValue
  have selectNotEqualValue : hierStep.childOutputs .selectNotEqual .result =
      bif hierStep.inputs .instr_bne then !(equal (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2))
      else bif hierStep.inputs .instr_bge then !(sharedSignedLess (valuesOf hierStep.inputs))
      else bif hierStep.inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf hierStep.inputs))
      else bif hierStep.inputs .is_slti_blt_slt then sharedSignedLess (valuesOf hierStep.inputs)
      else bif hierStep.inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf hierStep.inputs)
      else false := by
    have equation := Modules.Mux.result_of_allowed .bit
      (childMatch .selectNotEqual).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    exact mux_congr equation rfl notEqualValue selectSignedGreaterEqualValue
  have selectEqualValue : hierStep.childOutputs .selectEqual .result =
      comparisonOutput (valuesOf hierStep.inputs) := by
    have equation := Modules.Mux.result_of_allowed .bit
      (childMatch .selectEqual).allowed
    simp only [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    have equalityAsBool :
        hierStep.childOutputs .equality .result =
          equal (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) :=
      equalityValue.trans (equal_eq_signalEqual _ _).symm
    have selected := mux_congr equation rfl equalityAsBool selectNotEqualValue
    exact selected.trans rfl
  have comparisonWordValue : hierStep.childOutputs .comparisonWord .value =
      wordOfBool (comparisonOutput (valuesOf hierStep.inputs)) := by
    have equation := (wordCombiner.outputRule_holds_iff _ _ _).mp
      ((childMatch .comparisonWord).ruleHolds .apply)
    have valueEquation := congrFun equation .value
    funext index
    change Fin 32 at index
    have bitEquation := congrFun valueEquation index
    by_cases first : index = 0
    · subst index
      have normalized :
          hierStep.childOutputs .comparisonWord .value 0 =
            hierStep.childOutputs .selectEqual .result := by
        simpa [Composition.SignalCombiner.outputValues, wordCombiner,
          Wiring.childInputValues, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using bitEquation
      simpa [wordOfBool] using normalized.trans selectEqualValue
    · have normalized :
          hierStep.childOutputs .comparisonWord .value index =
            hierStep.childOutputs .zeroBit .output := by
        simpa [Composition.SignalCombiner.outputValues, wordCombiner,
        Wiring.childInputValues, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value, first] using bitEquation
      simpa [wordOfBool, first] using normalized.trans zeroBitValueEquation
  have xorSelectedValue : hierStep.childOutputs .xorSelected .output =
      (hierStep.inputs .instr_xori || hierStep.inputs .instr_xor) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .xorSelected).ruleHolds .apply)
    simpa [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  have orSelectedValue : hierStep.childOutputs .orSelected .output =
      (hierStep.inputs .instr_ori || hierStep.inputs .instr_or) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .orSelected).ruleHolds .apply)
    simpa [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  have andSelectedValue : hierStep.childOutputs .andSelected .output =
      (hierStep.inputs .instr_andi || hierStep.inputs .instr_and) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .andSelected).ruleHolds .apply)
    simpa [Wiring.childInputValues, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  -- Follow the result-selection mux chain.  Intermediate expressions are
  -- inferred instead of restating the progressively larger nested `bif`.
  have selectAndValue := Modules.Mux.result_of_allowed wordType
    (childMatch .selectAnd).allowed
  normalize_child_hyp selectAndValue unfolding wiring, context
  have selectAndResolved := mux_congr selectAndValue andSelectedValue
    bitwiseAndValue zeroWordValueEquation
  have selectOrValue := Modules.Mux.result_of_allowed wordType
    (childMatch .selectOr).allowed
  normalize_child_hyp selectOrValue unfolding wiring, context
  have selectOrResolved := mux_congr selectOrValue orSelectedValue
    bitwiseOrValue selectAndResolved
  have selectXorValue := Modules.Mux.result_of_allowed wordType
    (childMatch .selectXor).allowed
  normalize_child_hyp selectXorValue unfolding wiring, context
  have bitwiseXorWord :
      hierStep.childOutputs .bitwiseXor .result =
        bitwiseXor (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) :=
    bitwiseXorValue.trans (wordType_bitwiseXor _ _)
  have selectXorResolved := mux_congr selectXorValue xorSelectedValue
    bitwiseXorWord selectOrResolved
  have selectComparisonValue := Modules.Mux.result_of_allowed wordType
    (childMatch .selectComparison).allowed
  normalize_child_hyp selectComparisonValue unfolding wiring, context
  have selectComparisonResolved := mux_congr selectComparisonValue rfl
    comparisonWordValue selectXorResolved
  have selectArithmeticValue := Modules.Mux.result_of_allowed wordType
    (childMatch .selectArithmetic).allowed
  normalize_child_hyp selectArithmeticValue unfolding wiring, context
  have selectArithmeticResolved := mux_congr selectArithmeticValue rfl
    addSubResult selectComparisonResolved
  have aluOutBoundary : hierStep.outputs .alu_out =
      hierStep.childOutputs .selectArithmetic .result := by
    simpa [body, wiring, context, EndpointContext.instanceOutput, SignalSource.value] using
      satisfies.1 .alu_out
  have aluOut0Boundary : hierStep.outputs .alu_out_0 =
      hierStep.childOutputs .selectEqual .result := by
    simpa [body, wiring, context, EndpointContext.instanceOutput, SignalSource.value] using
      satisfies.1 .alu_out_0
  have addSubBehavior (subtract : Bool) :
      addSub subtract (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) =
        (Modules.AddSub.addSubBits 32 (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) subtract).1 := by
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
    · change hierStep.outputs .alu_out = aluOut (valuesOf hierStep.inputs)
      exact aluOutBoundary.trans (selectArithmeticResolved.trans <| by
        rw [aluOut_valuesOf]
        rw [← addSubBehavior (hierStep.inputs .instr_sub || hierStep.inputs .is_compare)]
        rfl)
    · change hierStep.outputs .alu_out_0 = aluOut0 (valuesOf hierStep.inputs)
      exact aluOut0Boundary.trans (selectEqualValue.trans rfl)
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

end Silean.Examples.PicoRV.Alu
