import PicoRV.Alu
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.AddSub.AddSubTheorems
import Silean.Modules.Equality.EqualityTheorems
import Silean.Modules.Mux.MuxTheorems

/-! Internal schedules and structural certification for the PicoRV ALU. -/

namespace PicoRV.Alu

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

private theorem equal_eq_signalEqual (left right : Word) :
    equal left right = (Silean.SignalType.vector 32 .bit).equal left right := by
  apply Bool.eq_iff_iff.mpr
  rw [Silean.SignalType.equal_eq_true_iff]
  simp only [equal, decide_eq_true_eq]
  constructor
  · exact fun equality => (Silean.BitVector.toNat_injective 32) equality
  · exact congrArg (Silean.BitVector.toNat 32)

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
    (Silean.SignalType.vector 32 .bit).bitwiseXor left right = bitwiseXor left right := by
  funext index
  simp only [Silean.SignalType.bitwiseXor, bitwiseXor]
  cases left index <;> cases right index <;> rfl

private theorem primitiveXor_eq_boolXor (left right : Bool) :
    Silean.Primitives.xorValue left right = Bool.xor left right := by
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
  subtractMode := Silean.Primitives.orCertified.certification,
  addSub := Silean.Modules.AddSub.certification 32,
  equality := Silean.Modules.Equality.certification wordType,
  bitwiseXor := Silean.Modules.BitwiseXor.certification wordType,
  bitwiseOr := Silean.Modules.BitwiseOr.certification wordType,
  bitwiseAnd := Silean.Modules.BitwiseAnd.certification wordType,
  zeroBit := Silean.Modules.Constant.certification .bit zeroBitValue,
  zeroWord := Silean.Modules.Constant.certification wordType zeroWordValue,
  unsignedLess := Silean.Primitives.notCertified.certification,
  signDifference := Silean.Primitives.xorCertified.certification,
  signedLess := Silean.Modules.Mux.certification .bit,
  notEqual := Silean.Primitives.notCertified.certification,
  notSignedLess := Silean.Primitives.notCertified.certification,
  notUnsignedLess := Silean.Primitives.notCertified.certification,
  selectUnsignedLess := Silean.Modules.Mux.certification .bit,
  selectSignedLess := Silean.Modules.Mux.certification .bit,
  selectUnsignedGreaterEqual := Silean.Modules.Mux.certification .bit,
  selectSignedGreaterEqual := Silean.Modules.Mux.certification .bit,
  selectNotEqual := Silean.Modules.Mux.certification .bit,
  selectEqual := Silean.Modules.Mux.certification .bit,
  comparisonWord := wordCombiner.certified.certification,
  xorSelected := Silean.Primitives.orCertified.certification,
  orSelected := Silean.Primitives.orCertified.certification,
  andSelected := Silean.Primitives.orCertified.certification,
  selectAnd := Silean.Modules.Mux.certification wordType,
  selectOr := Silean.Modules.Mux.certification wordType,
  selectXor := Silean.Modules.Mux.certification wordType,
  selectComparison := Silean.Modules.Mux.certification wordType,
  selectArithmetic := Silean.Modules.Mux.certification wordType

/-! ## Cycle certification -/

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [.leftSplit => Silean.Composition.SignalComponentRule.apply,
        .rightSplit => Silean.Composition.SignalComponentRule.apply,
        .subtractMode => Silean.Primitives.OrRule.apply,
        .addSub => Silean.Modules.AddSub.Rule.apply,
        .equality => Silean.Modules.Equality.Rule.apply,
        .bitwiseXor => Silean.Modules.BitwiseXor.Rule.apply,
        .bitwiseOr => Silean.Modules.BitwiseOr.Rule.apply,
        .bitwiseAnd => Silean.Modules.BitwiseAnd.Rule.apply,
        .zeroBit => Silean.Primitives.ConstantRule.apply,
        .zeroWord => Silean.Primitives.ConstantRule.apply,
        .unsignedLess => Silean.Primitives.NotRule.apply,
        .signDifference => Silean.Primitives.XorRule.apply,
        .signedLess => Silean.Modules.Mux.Rule.select,
        .notEqual => Silean.Primitives.NotRule.apply,
        .notSignedLess => Silean.Primitives.NotRule.apply,
        .notUnsignedLess => Silean.Primitives.NotRule.apply,
        .selectUnsignedLess => Silean.Modules.Mux.Rule.select,
        .selectSignedLess => Silean.Modules.Mux.Rule.select,
        .selectUnsignedGreaterEqual => Silean.Modules.Mux.Rule.select,
        .selectSignedGreaterEqual => Silean.Modules.Mux.Rule.select,
        .selectNotEqual => Silean.Modules.Mux.Rule.select,
        .selectEqual => Silean.Modules.Mux.Rule.select,
        .comparisonWord => Silean.Composition.SignalComponentRule.apply,
        .xorSelected => Silean.Primitives.OrRule.apply,
        .orSelected => Silean.Primitives.OrRule.apply,
        .andSelected => Silean.Primitives.OrRule.apply,
        .selectAnd => Silean.Modules.Mux.Rule.select,
        .selectOr => Silean.Modules.Mux.Rule.select,
        .selectXor => Silean.Modules.Mux.Rule.select,
        .selectComparison => Silean.Modules.Mux.Rule.select,
        .selectArithmetic => Silean.Modules.Mux.Rule.select]
  state := []

section LayerCertification

variable (layerChildren : Silean.Contracts.Cycle.Certification.Layer.ChildStructures
  body childContracts)

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
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
    simpa [Silean.Wiring.childInputValues, body, wiring, context, Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.Composition.SignalSplitter.outputValues, wordSplitter, Silean.SignalSource.value] using equation
  have rightSign : hierStep.childOutputs .rightSplit (Fin.last 31) = hierStep.inputs .reg_op2 31 := by
    have equation := congrFun rightSplitEquation (Fin.last 31)
    simpa [Silean.Wiring.childInputValues, body, wiring, context, Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.Composition.SignalSplitter.outputValues, wordSplitter, Silean.SignalSource.value] using equation
  have subtractModeValue : hierStep.childOutputs .subtractMode .output =
      (hierStep.inputs .instr_sub || hierStep.inputs .is_compare) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .subtractMode).ruleHolds .apply)
    simpa [Silean.Wiring.childInputValues, body, wiring, context, Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using equation
  have addSubResult : hierStep.childOutputs .addSub .result =
      (Silean.Modules.AddSub.addSubBits 32 (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2)
        (hierStep.inputs .instr_sub || hierStep.inputs .is_compare)).1 := by
    have equation :=
      (Silean.Modules.AddSub.Behavior.of_allowed 32 (childMatch .addSub).allowed).result
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun subtract => (Silean.Modules.AddSub.addSubBits 32
        (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) subtract).1)
      subtractModeValue)
  have addSubCarry : hierStep.childOutputs .addSub .carryOut =
      (Silean.Modules.AddSub.addSubBits 32 (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2)
        (hierStep.inputs .instr_sub || hierStep.inputs .is_compare)).2 := by
    have equation :=
      (Silean.Modules.AddSub.Behavior.of_allowed 32 (childMatch .addSub).allowed).carryOut
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg
      (fun subtract => (Silean.Modules.AddSub.addSubBits 32
        (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) subtract).2)
      subtractModeValue)
  child_contract_fact equalityValue : hierStep.childOutputs .equality .result =
      wordType.equal (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) from
      (childMatch .equality).allowed using
      Silean.Modules.Equality.result_of_allowed wordType unfolding body, wiring, context
  child_contract_fact bitwiseXorValue : hierStep.childOutputs .bitwiseXor .result =
      wordType.bitwiseXor (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) from
      (childMatch .bitwiseXor).allowed using
      Silean.Modules.BitwiseXor.result_of_allowed wordType unfolding body, wiring, context
  child_contract_fact bitwiseOrValue : hierStep.childOutputs .bitwiseOr .result =
      wordType.bitwiseOr (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) from
      (childMatch .bitwiseOr).allowed using
      Silean.Modules.BitwiseOr.result_of_allowed wordType unfolding body, wiring, context
  child_contract_fact bitwiseAndValue : hierStep.childOutputs .bitwiseAnd .result =
      wordType.bitwiseAnd (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) from
      (childMatch .bitwiseAnd).allowed using
      Silean.Modules.BitwiseAnd.result_of_allowed wordType unfolding body, wiring, context
  have zeroBitValueEquation : hierStep.childOutputs .zeroBit .output = false := by
    have equation := Silean.Modules.Constant.output_of_allowed .bit zeroBitValue
      (childMatch .zeroBit).allowed
    simpa [zeroBitValue] using equation
  have zeroWordValueEquation : hierStep.childOutputs .zeroWord .output = wordOfNat 0 := by
    have equation := Silean.Modules.Constant.output_of_allowed wordType zeroWordValue
      (childMatch .zeroWord).allowed
    simpa [zeroWordValue] using equation
  have unsignedLessValue : hierStep.childOutputs .unsignedLess .output =
      sharedUnsignedLess (valuesOf hierStep.inputs) := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .unsignedLess).ruleHolds .apply)
    have normalized : hierStep.childOutputs .unsignedLess .output =
        !(hierStep.childOutputs .addSub .carryOut) := by
      simpa [Silean.Wiring.childInputValues, body, wiring, context,
        Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
        Silean.SignalSource.value] using equation
    exact normalized.trans (congrArg Bool.not addSubCarry)
  have signDifferenceValue : hierStep.childOutputs .signDifference .output =
      Bool.xor (hierStep.inputs .reg_op1 31) (hierStep.inputs .reg_op2 31) := by
    have equation := (Silean.Primitives.xorOutputRule_holds_iff _ _ _).mp
      ((childMatch .signDifference).ruleHolds .apply)
    have normalized : hierStep.childOutputs .signDifference .output =
        Silean.Primitives.xorValue (hierStep.childOutputs .leftSplit (Fin.last 31))
          (hierStep.childOutputs .rightSplit (Fin.last 31)) := by
      simpa [Silean.Wiring.childInputValues, body, wiring, context,
        Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
        Silean.SignalSource.value] using equation
    exact (normalized.trans
      (apply₂_congr Silean.Primitives.xorValue leftSign rightSign)).trans
      (primitiveXor_eq_boolXor _ _)
  have signedLessValue : hierStep.childOutputs .signedLess .result =
      sharedSignedLess (valuesOf hierStep.inputs) := by
    have equation := Silean.Modules.Mux.result_of_allowed .bit
      (childMatch .signedLess).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
      Silean.SignalSource.value] at equation
    have selected := mux_congr equation signDifferenceValue leftSign unsignedLessValue
    exact selected.trans <| by
      cases left : hierStep.inputs .reg_op1 31 <;>
        cases right : hierStep.inputs .reg_op2 31 <;>
          simp [sharedSignedLess, valuesOf, left, right]
  have notEqualValue : hierStep.childOutputs .notEqual .output =
      !(equal (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2)) := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notEqual).ruleHolds .apply)
    have normalized : hierStep.childOutputs .notEqual .output =
        !(hierStep.childOutputs .equality .result) := by
      simpa [Silean.Wiring.childInputValues, body, wiring, context,
        Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
        Silean.SignalSource.value] using equation
    exact normalized.trans ((congrArg Bool.not equalityValue).trans
      (congrArg Bool.not (equal_eq_signalEqual _ _).symm))
  have notSignedLessValue : hierStep.childOutputs .notSignedLess .output =
      !(sharedSignedLess (valuesOf hierStep.inputs)) := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notSignedLess).ruleHolds .apply)
    have normalized : hierStep.childOutputs .notSignedLess .output =
        !(hierStep.childOutputs .signedLess .result) := by
      simpa [Silean.Wiring.childInputValues, body, wiring, context,
        Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
        Silean.SignalSource.value] using equation
    exact normalized.trans (congrArg Bool.not signedLessValue)
  have notUnsignedLessValue : hierStep.childOutputs .notUnsignedLess .output =
      !(sharedUnsignedLess (valuesOf hierStep.inputs)) := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notUnsignedLess).ruleHolds .apply)
    have normalized : hierStep.childOutputs .notUnsignedLess .output =
        !(hierStep.childOutputs .unsignedLess .output) := by
      simpa [Silean.Wiring.childInputValues, body, wiring, context,
        Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput,
        Silean.SignalSource.value] using equation
    exact normalized.trans (congrArg Bool.not unsignedLessValue)
  have selectUnsignedLessValue : hierStep.childOutputs .selectUnsignedLess .result =
      bif hierStep.inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf hierStep.inputs) else false := by
    have equation := Silean.Modules.Mux.result_of_allowed .bit
      (childMatch .selectUnsignedLess).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] at equation
    exact mux_congr equation rfl unsignedLessValue zeroBitValueEquation
  have selectSignedLessValue : hierStep.childOutputs .selectSignedLess .result =
      bif hierStep.inputs .is_slti_blt_slt then sharedSignedLess (valuesOf hierStep.inputs)
      else bif hierStep.inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf hierStep.inputs) else false := by
    have equation := Silean.Modules.Mux.result_of_allowed .bit
      (childMatch .selectSignedLess).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] at equation
    exact mux_congr equation rfl signedLessValue selectUnsignedLessValue
  have selectUnsignedGreaterEqualValue :
      hierStep.childOutputs .selectUnsignedGreaterEqual .result =
        bif hierStep.inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf hierStep.inputs))
        else bif hierStep.inputs .is_slti_blt_slt then sharedSignedLess (valuesOf hierStep.inputs)
        else bif hierStep.inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf hierStep.inputs)
        else false := by
    have equation := Silean.Modules.Mux.result_of_allowed .bit
      (childMatch .selectUnsignedGreaterEqual).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] at equation
    exact mux_congr equation rfl notUnsignedLessValue selectSignedLessValue
  have selectSignedGreaterEqualValue :
      hierStep.childOutputs .selectSignedGreaterEqual .result =
        bif hierStep.inputs .instr_bge then !(sharedSignedLess (valuesOf hierStep.inputs))
        else bif hierStep.inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf hierStep.inputs))
        else bif hierStep.inputs .is_slti_blt_slt then sharedSignedLess (valuesOf hierStep.inputs)
        else bif hierStep.inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf hierStep.inputs)
        else false := by
    have equation := Silean.Modules.Mux.result_of_allowed .bit
      (childMatch .selectSignedGreaterEqual).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] at equation
    exact mux_congr equation rfl notSignedLessValue
      selectUnsignedGreaterEqualValue
  have selectNotEqualValue : hierStep.childOutputs .selectNotEqual .result =
      bif hierStep.inputs .instr_bne then !(equal (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2))
      else bif hierStep.inputs .instr_bge then !(sharedSignedLess (valuesOf hierStep.inputs))
      else bif hierStep.inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf hierStep.inputs))
      else bif hierStep.inputs .is_slti_blt_slt then sharedSignedLess (valuesOf hierStep.inputs)
      else bif hierStep.inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf hierStep.inputs)
      else false := by
    have equation := Silean.Modules.Mux.result_of_allowed .bit
      (childMatch .selectNotEqual).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] at equation
    exact mux_congr equation rfl notEqualValue selectSignedGreaterEqualValue
  have selectEqualValue : hierStep.childOutputs .selectEqual .result =
      comparisonOutput (valuesOf hierStep.inputs) := by
    have equation := Silean.Modules.Mux.result_of_allowed .bit
      (childMatch .selectEqual).allowed
    simp only [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] at equation
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
        simpa [Silean.Composition.SignalCombiner.outputValues, wordCombiner,
          Silean.Wiring.childInputValues, body, wiring, context,
          Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using bitEquation
      simpa [wordOfBool] using normalized.trans selectEqualValue
    · have normalized :
          hierStep.childOutputs .comparisonWord .value index =
            hierStep.childOutputs .zeroBit .output := by
        simpa [Silean.Composition.SignalCombiner.outputValues, wordCombiner,
        Silean.Wiring.childInputValues, body, wiring, context,
          Silean.EndpointContext.instanceOutput, Silean.SignalSource.value, first] using bitEquation
      simpa [wordOfBool, first] using normalized.trans zeroBitValueEquation
  have xorSelectedValue : hierStep.childOutputs .xorSelected .output =
      (hierStep.inputs .instr_xori || hierStep.inputs .instr_xor) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .xorSelected).ruleHolds .apply)
    simpa [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using equation
  have orSelectedValue : hierStep.childOutputs .orSelected .output =
      (hierStep.inputs .instr_ori || hierStep.inputs .instr_or) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .orSelected).ruleHolds .apply)
    simpa [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using equation
  have andSelectedValue : hierStep.childOutputs .andSelected .output =
      (hierStep.inputs .instr_andi || hierStep.inputs .instr_and) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .andSelected).ruleHolds .apply)
    simpa [Silean.Wiring.childInputValues, body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using equation
  -- Follow the result-selection mux chain.  Intermediate expressions are
  -- inferred instead of restating the progressively larger nested `bif`.
  have selectAndValue := Silean.Modules.Mux.result_of_allowed wordType
    (childMatch .selectAnd).allowed
  normalize_child_hyp selectAndValue unfolding wiring, context
  have selectAndResolved := mux_congr selectAndValue andSelectedValue
    bitwiseAndValue zeroWordValueEquation
  have selectOrValue := Silean.Modules.Mux.result_of_allowed wordType
    (childMatch .selectOr).allowed
  normalize_child_hyp selectOrValue unfolding wiring, context
  have selectOrResolved := mux_congr selectOrValue orSelectedValue
    bitwiseOrValue selectAndResolved
  have selectXorValue := Silean.Modules.Mux.result_of_allowed wordType
    (childMatch .selectXor).allowed
  normalize_child_hyp selectXorValue unfolding wiring, context
  have bitwiseXorWord :
      hierStep.childOutputs .bitwiseXor .result =
        bitwiseXor (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) :=
    bitwiseXorValue.trans (wordType_bitwiseXor _ _)
  have selectXorResolved := mux_congr selectXorValue xorSelectedValue
    bitwiseXorWord selectOrResolved
  have selectComparisonValue := Silean.Modules.Mux.result_of_allowed wordType
    (childMatch .selectComparison).allowed
  normalize_child_hyp selectComparisonValue unfolding wiring, context
  have selectComparisonResolved := mux_congr selectComparisonValue rfl
    comparisonWordValue selectXorResolved
  have selectArithmeticValue := Silean.Modules.Mux.result_of_allowed wordType
    (childMatch .selectArithmetic).allowed
  normalize_child_hyp selectArithmeticValue unfolding wiring, context
  have selectArithmeticResolved := mux_congr selectArithmeticValue rfl
    addSubResult selectComparisonResolved
  have aluOutBoundary : hierStep.outputs .alu_out =
      hierStep.childOutputs .selectArithmetic .result := by
    simpa [body, wiring, context, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using
      satisfies.1 .alu_out
  have aluOut0Boundary : hierStep.outputs .alu_out_0 =
      hierStep.childOutputs .selectEqual .result := by
    simpa [body, wiring, context, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using
      satisfies.1 .alu_out_0
  have addSubBehavior (subtract : Bool) :
      addSub subtract (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) =
        (Silean.Modules.AddSub.addSubBits 32 (hierStep.inputs .reg_op1) (hierStep.inputs .reg_op2) subtract).1 := by
    apply Silean.BitVector.toNat_injective 32
    rw [Silean.Modules.AddSub.addSubBits_result_toNat]
    cases subtract <;>
      simp [addSub, wordOfNat, Silean.BitVector.toNat_ofNat]
  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
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
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState :=
  ⟨Silean.SignalMap.emptyValues, trivial⟩

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

end PicoRV.Alu
