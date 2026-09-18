import PicoRV.Datapath.DatapathShiftUpdate
import PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.AddSub.AddSubTheorems
import Silean.Modules.EqualsConstant.EqualsConstantTheorems
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.VectorLayout.VectorLayoutTheorems
import Silean.Primitives.Or

namespace PicoRV.Datapath.ShiftUpdate

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  amountBits := amountSplitter.certified.certification,
  amountHigh23 := Silean.Primitives.orCertified.certification,
  amountGeFour := Silean.Primitives.orCertified.certification,
  amountZero := Silean.Modules.EqualsConstant.certification (.vector 5 .bit)
    (fiveBitsOfNat 0),
  leftSelect := Silean.Primitives.orCertified.certification,
  logicalSelect := Silean.Primitives.orCertified.certification,
  arithmeticSelect := Silean.Primitives.orCertified.certification,
  trueBit := Silean.Modules.Constant.certification .bit true,
  leftOne := Silean.Modules.VectorLayout.certification 32 32 (leftLayout 1),
  leftFour := Silean.Modules.VectorLayout.certification 32 32 (leftLayout 4),
  logicalOne := Silean.Modules.VectorLayout.certification 32 32 (rightLogicalLayout 1),
  logicalFour := Silean.Modules.VectorLayout.certification 32 32 (rightLogicalLayout 4),
  arithmeticOne := Silean.Modules.VectorLayout.certification 32 32
    (rightArithmeticLayout 1),
  arithmeticFour := Silean.Modules.VectorLayout.certification 32 32
    (rightArithmeticLayout 4),
  selectedLeft := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectedLogical := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectedArithmetic := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectArithmetic := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectLogical := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectLeft := Silean.Modules.Mux.certification (.vector 32 .bit),
  one := Silean.Modules.Constant.certification (.vector 5 .bit) (fiveBitsOfNat 1),
  four := Silean.Modules.Constant.certification (.vector 5 .bit) (fiveBitsOfNat 4),
  selectedStep := Silean.Modules.Mux.certification (.vector 5 .bit),
  subtractStep := Silean.Modules.AddSub.certification 5,
  selectedOp1 := Silean.Modules.Mux.certification (.vector 32 .bit),
  selectedShift := Silean.Modules.Mux.certification (.vector 5 .bit),
  selectedResult := Silean.Modules.Mux.certification (.vector 32 .bit),
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Silean.Modules.NamedTupleSplitter.Rule.apply,
    .amountBits => Silean.Composition.SignalComponentRule.apply,
    {.amountHigh23, .amountGeFour, .leftSelect, .logicalSelect,
      .arithmeticSelect} => Silean.Primitives.OrRule.apply,
    .amountZero => Silean.Modules.EqualsConstant.Rule.apply,
    {.trueBit, .one, .four} => Silean.Primitives.ConstantRule.apply,
    {.leftOne, .leftFour, .logicalOne, .logicalFour,
      .arithmeticOne, .arithmeticFour} => Silean.Modules.VectorLayout.Rule.apply,
    {.selectedLeft, .selectedLogical, .selectedArithmetic, .selectArithmetic,
      .selectLogical, .selectLeft, .selectedStep} => Silean.Modules.Mux.Rule.select,
    .subtractStep => Silean.Modules.AddSub.Rule.apply,
    {.selectedOp1, .selectedShift, .selectedResult} => Silean.Modules.Mux.Rule.select,
    .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
  state := []

theorem left_layout (word : Word) (amount : Nat) :
    Silean.Modules.VectorLayout.apply (leftLayout amount) word = shiftLeft word amount := by
  funext index
  by_cases low : index.val < amount <;>
    simp [Silean.Modules.VectorLayout.apply, leftLayout, shiftLeft, low]

theorem logical_layout (word : Word) (amount : Nat) :
    Silean.Modules.VectorLayout.apply (rightLogicalLayout amount) word =
      shiftRightLogical word amount := by
  funext index
  by_cases high : index.val + amount < 32 <;>
    simp [Silean.Modules.VectorLayout.apply, rightLogicalLayout, shiftRightLogical, high]

theorem arithmetic_layout (word : Word) (amount : Nat) :
    Silean.Modules.VectorLayout.apply (rightArithmeticLayout amount) word =
      shiftRightArithmetic word amount := by
  funext index
  by_cases high : index.val + amount < 32 <;>
    simp [Silean.Modules.VectorLayout.apply, rightArithmeticLayout,
      shiftRightArithmetic, high]

private theorem high_bits_mean_ge_four : ∀ bits : FiveBits,
    (bits 2 || bits 3 || bits 4) = decide (Silean.BitVector.toNat 5 bits ≥ 4) := by
  intro bits
  have lowBound := Silean.BitVector.toNat_lt_cardinality 2
    (fun index => bits index.castSucc.castSucc.castSucc)
  cases bit4 : bits 4 <;> cases bit3 : bits 3 <;> cases bit2 : bits 2 <;>
    simp [Silean.BitVector.toNat, Silean.BitVector.cardinality, bit4, bit3, bit2] at lowBound ⊢ <;>
    omega

private theorem signal_equal_zero : ∀ bits : FiveBits,
    (Silean.SignalType.vector 5 .bit).equal bits (fiveBitsOfNat 0) =
      decide (Silean.BitVector.toNat 5 bits = 0) := by
  intro bits
  apply Bool.eq_iff_iff.mpr
  rw [Silean.SignalType.equal_eq_true_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro rfl
    simp [fiveBitsOfNat, Silean.BitVector.toNat]
  · intro zero
    apply Silean.BitVector.toNat_injective 5
    rw [zero]
    simp [fiveBitsOfNat, Silean.BitVector.toNat]

private theorem subtract_selected_step : ∀ bits : FiveBits,
    Silean.BitVector.toNat 5 bits ≠ 0 →
      (Silean.Modules.AddSub.addSubBits 5 bits
        (bif bits 2 || bits 3 || bits 4 then fiveBitsOfNat 4
          else fiveBitsOfNat 1) true).1 =
        fiveBitsOfNat (Silean.BitVector.toNat 5 bits -
          if Silean.BitVector.toNat 5 bits ≥ 4 then 4 else 1) := by
  intro bits nonzero
  apply Silean.BitVector.toNat_injective 5
  rw [Silean.Modules.AddSub.addSubBits_result_toNat]
  simp only [if_true]
  have amountBound := Silean.BitVector.toNat_lt_cardinality 5 bits
  have highMeaning := high_bits_mean_ge_four bits
  cases high : bits 2 || bits 3 || bits 4
  · rw [high] at highMeaning
    have small : Silean.BitVector.toNat 5 bits < 4 := by simpa using highMeaning
    have positive : 1 ≤ Silean.BitVector.toNat 5 bits := by omega
    simp [show ¬ Silean.BitVector.toNat 5 bits ≥ 4 by omega]
    change (Silean.BitVector.toNat 5 bits + Silean.BitVector.cardinality 5 -
        Silean.BitVector.toNat 5 (fiveBitsOfNat 1)) % Silean.BitVector.cardinality 5 =
      Silean.BitVector.toNat 5 (fiveBitsOfNat (Silean.BitVector.toNat 5 bits - 1))
    rw [show fiveBitsOfNat 1 = Silean.BitVector.ofNat 5 1 by rfl,
      show fiveBitsOfNat (Silean.BitVector.toNat 5 bits - 1) =
        Silean.BitVector.ofNat 5 (Silean.BitVector.toNat 5 bits - 1) by rfl]
    rw [Silean.BitVector.toNat_ofNat, Silean.BitVector.toNat_ofNat]
    rw [show Silean.BitVector.cardinality 5 = 32 by decide] at amountBound ⊢
    have sum : Silean.BitVector.toNat 5 bits + 32 - 1 =
        (Silean.BitVector.toNat 5 bits - 1) + 32 := by omega
    rw [sum, Nat.add_mod, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt (by omega : Silean.BitVector.toNat 5 bits - 1 < 32)]
    exact Nat.mod_eq_of_lt (by omega)
  · have large : 4 ≤ Silean.BitVector.toNat 5 bits := by
      simpa [high] using highMeaning
    simp [large]
    change (Silean.BitVector.toNat 5 bits + Silean.BitVector.cardinality 5 -
        Silean.BitVector.toNat 5 (fiveBitsOfNat 4)) % Silean.BitVector.cardinality 5 =
      Silean.BitVector.toNat 5 (fiveBitsOfNat (Silean.BitVector.toNat 5 bits - 4))
    rw [show fiveBitsOfNat 4 = Silean.BitVector.ofNat 5 4 by rfl,
      show fiveBitsOfNat (Silean.BitVector.toNat 5 bits - 4) =
        Silean.BitVector.ofNat 5 (Silean.BitVector.toNat 5 bits - 4) by rfl]
    rw [Silean.BitVector.toNat_ofNat, Silean.BitVector.toNat_ofNat]
    rw [show Silean.BitVector.cardinality 5 = 32 by decide] at amountBound ⊢
    have sum : Silean.BitVector.toNat 5 bits + 32 - 4 =
        (Silean.BitVector.toNat 5 bits - 4) + 32 := by omega
    rw [sum, Nat.add_mod, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt (by omega : Silean.BitVector.toNat 5 bits - 4 < 32)]
    exact Nat.mod_eq_of_lt (by omega)

def selectedStepAmount (current : stateMap.Values) : Nat :=
  if shiftAmount current ≥ 4 then 4 else 1

def shiftedStep (inputs : Inputs) (current : stateMap.Values) : Word :=
  shiftedValue inputs (current .reg_op1) (selectedStepAmount current)

def structuralState (inputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values :=
  if shiftAmount current = 0 then
    stateMap.set updated .reg_out (current .reg_op1)
  else
    let next := stateMap.set updated .reg_op1 (shiftedStep inputs current)
    stateMap.set next .reg_sh
      (fiveBitsOfNat (shiftAmount current - selectedStepAmount current))

theorem structuralState_eq_shiftNextState (inputs : Inputs)
    (current updated : stateMap.Values) :
    structuralState inputs current updated = shiftNextState inputs current updated := by
  cases amount : shiftAmount current with
  | zero => simp [structuralState, shiftNextState, amount]
  | succ amount =>
      simp [structuralState, shiftNextState, shiftedStep, selectedStepAmount,
        amount]

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
    rw [inputsFieldsValue]
    cases field <;> rfl

  have amountSplit := (amountSplitter.outputRule_holds_iff _ _ _).mp
    ((childMatch .amountBits).ruleHolds Silean.Composition.SignalComponentRule.apply)
  have amountBit (index : Fin 5) :
      hierStep.childOutputs .amountBits index = current .reg_sh index := by
    have equation := congrFun amountSplit index
    have wired : hierStep.childOutputs .amountBits index =
        hierStep.childOutputs .currentFields .reg_sh index := by
      simpa [Silean.Composition.SignalSplitter.outputValues, amountSplitter,
        body, wiring, context,
        Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using equation
    rw [wired, congrFun currentFieldsValue .reg_sh]
  have high23Value : hierStep.childOutputs .amountHigh23 .output =
      (current .reg_sh 2 || current .reg_sh 3) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .amountHigh23).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [amountBit 2, amountBit 3] at equation
    exact equation
  have geFourValue : hierStep.childOutputs .amountGeFour .output =
      decide (shiftAmount current ≥ 4) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .amountGeFour).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [high23Value, amountBit 4] at equation
    rw [equation]
    exact high_bits_mean_ge_four (current .reg_sh)
  have zeroValue : hierStep.childOutputs .amountZero .result =
      decide (shiftAmount current = 0) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 5 .bit) (fiveBitsOfNat 0) _ _ _).mp
      ((childMatch .amountZero).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue] at equation
    rw [equation]
    exact signal_equal_zero (current .reg_sh)

  have leftSelectValue : hierStep.childOutputs .leftSelect .output =
      (datapathInputs.instr_slli || datapathInputs.instr_sll) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .leftSelect).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [inputField .instr_slli, inputField .instr_sll] at equation
    exact equation
  have logicalSelectValue : hierStep.childOutputs .logicalSelect .output =
      (datapathInputs.instr_srli || datapathInputs.instr_srl) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .logicalSelect).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [inputField .instr_srli, inputField .instr_srl] at equation
    exact equation
  have arithmeticSelectValue : hierStep.childOutputs .arithmeticSelect .output =
      (datapathInputs.instr_srai || datapathInputs.instr_sra) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmeticSelect).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [inputField .instr_srai, inputField .instr_sra] at equation
    exact equation

  have leftOneValue : hierStep.childOutputs .leftOne .output =
      shiftLeft (current .reg_op1) 1 := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 32
      (leftLayout 1) (childMatch .leftOne).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue, left_layout] at equation
    exact equation
  have leftFourValue : hierStep.childOutputs .leftFour .output =
      shiftLeft (current .reg_op1) 4 := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 32
      (leftLayout 4) (childMatch .leftFour).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue, left_layout] at equation
    exact equation
  have logicalOneValue : hierStep.childOutputs .logicalOne .output =
      shiftRightLogical (current .reg_op1) 1 := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 32
      (rightLogicalLayout 1) (childMatch .logicalOne).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue, logical_layout] at equation
    exact equation
  have logicalFourValue : hierStep.childOutputs .logicalFour .output =
      shiftRightLogical (current .reg_op1) 4 := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 32
      (rightLogicalLayout 4) (childMatch .logicalFour).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue, logical_layout] at equation
    exact equation
  have arithmeticOneValue : hierStep.childOutputs .arithmeticOne .output =
      shiftRightArithmetic (current .reg_op1) 1 := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 32
      (rightArithmeticLayout 1) (childMatch .arithmeticOne).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue, arithmetic_layout] at equation
    exact equation
  have arithmeticFourValue : hierStep.childOutputs .arithmeticFour .output =
      shiftRightArithmetic (current .reg_op1) 4 := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 32
      (rightArithmeticLayout 4) (childMatch .arithmeticFour).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue, arithmetic_layout] at equation
    exact equation

  have selectedLeftValue : hierStep.childOutputs .selectedLeft .result =
      shiftLeft (current .reg_op1) (selectedStepAmount current) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectedLeft).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [geFourValue, leftOneValue, leftFourValue] at equation
    by_cases large : shiftAmount current ≥ 4
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
  have selectedLogicalValue : hierStep.childOutputs .selectedLogical .result =
      shiftRightLogical (current .reg_op1) (selectedStepAmount current) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectedLogical).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [geFourValue, logicalOneValue, logicalFourValue] at equation
    by_cases large : shiftAmount current ≥ 4
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
  have selectedArithmeticValue : hierStep.childOutputs .selectedArithmetic .result =
      shiftRightArithmetic (current .reg_op1) (selectedStepAmount current) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectedArithmetic).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [geFourValue, arithmeticOneValue, arithmeticFourValue] at equation
    by_cases large : shiftAmount current ≥ 4
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
  have selectArithmeticValue : hierStep.childOutputs .selectArithmetic .result =
      (if datapathInputs.instr_srai || datapathInputs.instr_sra then
        shiftRightArithmetic (current .reg_op1) (selectedStepAmount current)
      else current .reg_op1) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectArithmetic).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [arithmeticSelectValue, currentFieldsValue,
      selectedArithmeticValue] at equation
    cases arithmetic : datapathInputs.instr_srai || datapathInputs.instr_sra <;>
      simp [arithmetic] at equation ⊢ <;> exact equation
  have selectLogicalValue : hierStep.childOutputs .selectLogical .result =
      (if datapathInputs.instr_srli || datapathInputs.instr_srl then
        shiftRightLogical (current .reg_op1) (selectedStepAmount current)
      else if datapathInputs.instr_srai || datapathInputs.instr_sra then
        shiftRightArithmetic (current .reg_op1) (selectedStepAmount current)
      else current .reg_op1) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectLogical).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [logicalSelectValue, selectedLogicalValue,
      selectArithmeticValue] at equation
    cases logical : datapathInputs.instr_srli || datapathInputs.instr_srl <;>
      simp [logical] at equation ⊢ <;> exact equation
  have shiftedValueEquation : hierStep.childOutputs .selectLeft .result =
      shiftedStep datapathInputs current := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectLeft).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [leftSelectValue, selectedLeftValue, selectLogicalValue] at equation
    cases left : datapathInputs.instr_slli || datapathInputs.instr_sll <;>
      cases logical : datapathInputs.instr_srli || datapathInputs.instr_srl <;>
      cases arithmetic : datapathInputs.instr_srai || datapathInputs.instr_sra <;>
      simp [shiftedStep, shiftedValue, left, logical, arithmetic] at equation ⊢ <;>
      exact equation

  have trueValue := (Silean.Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).ruleHolds Silean.Primitives.ConstantRule.apply)
  have oneValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 5 .bit) (fiveBitsOfNat 1) _ _ _).mp
    ((childMatch .one).ruleHolds Silean.Primitives.ConstantRule.apply)
  have fourValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 5 .bit) (fiveBitsOfNat 4) _ _ _).mp
    ((childMatch .four).ruleHolds Silean.Primitives.ConstantRule.apply)
  have stepValue : hierStep.childOutputs .selectedStep .result =
      (if shiftAmount current ≥ 4 then fiveBitsOfNat 4 else fiveBitsOfNat 1) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 5 .bit)
      (childMatch .selectedStep).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [geFourValue, oneValue, fourValue] at equation
    by_cases large : shiftAmount current ≥ 4
    · simp [large] at equation ⊢
      exact equation
    · simp [large] at equation ⊢
      exact equation
  have subtractValue : hierStep.childOutputs .subtractStep .result =
      (Silean.Modules.AddSub.addSubBits 5 (current .reg_sh)
        (bif current .reg_sh 2 || current .reg_sh 3 || current .reg_sh 4 then
          fiveBitsOfNat 4 else fiveBitsOfNat 1) true).1 := by
    have equation :=
      (Silean.Modules.AddSub.Behavior.of_allowed 5
        (childMatch .subtractStep).allowed).result
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue, stepValue, trueValue] at equation
    have highMeaning := high_bits_mean_ge_four (current .reg_sh)
    cases high : current .reg_sh 2 || current .reg_sh 3 || current .reg_sh 4
    · have small : ¬ shiftAmount current ≥ 4 := by
        simpa [shiftAmount, high] using highMeaning
      simpa [high, small] using equation
    · have large : shiftAmount current ≥ 4 := by
        simpa [shiftAmount, high] using highMeaning
      simpa [high, large] using equation

  have selectedOp1Value : hierStep.childOutputs .selectedOp1 .result =
      (if shiftAmount current = 0 then updated .reg_op1
      else shiftedStep datapathInputs current) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectedOp1).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [zeroValue, shiftedValueEquation, updatedFieldsValue] at equation
    by_cases zero : shiftAmount current = 0
    · simp [zero] at equation ⊢
      exact equation
    · simp [zero] at equation ⊢
      exact equation
  have selectedShiftValue : hierStep.childOutputs .selectedShift .result =
      (if shiftAmount current = 0 then updated .reg_sh
      else fiveBitsOfNat
        (shiftAmount current - selectedStepAmount current)) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 5 .bit)
      (childMatch .selectedShift).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [zeroValue, subtractValue, updatedFieldsValue] at equation
    by_cases zero : shiftAmount current = 0
    · simp [zero] at equation ⊢
      exact equation
    · rw [subtract_selected_step (current .reg_sh) (by simpa [shiftAmount] using zero)]
        at equation
      have zeroDecision : decide (shiftAmount current = 0) = false := by
        exact decide_eq_false zero
      rw [zeroDecision] at equation
      simp [zero, selectedStepAmount] at equation ⊢
      exact equation
  have selectedResultValue : hierStep.childOutputs .selectedResult .result =
      (if shiftAmount current = 0 then current .reg_op1
      else updated .reg_out) := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .selectedResult).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [zeroValue, updatedFieldsValue, currentFieldsValue] at equation
    by_cases zero : shiftAmount current = 0
    · simp [zero] at equation ⊢
      exact equation
    · simp [zero] at equation ⊢
      exact equation

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result = structuralState datapathInputs current updated := by
    funext field
    by_cases zero : shiftAmount current = 0
    · cases field
      · change hierStep.childOutputs .updatedFields .reg_pc = _
        simpa [structuralState, zero, Silean.SignalMap.set] using
          congrFun updatedFieldsValue .reg_pc
      · change hierStep.childOutputs .updatedFields .reg_next_pc = _
        simpa [structuralState, zero, Silean.SignalMap.set] using
          congrFun updatedFieldsValue .reg_next_pc
      · change hierStep.childOutputs .selectedOp1 .result = _
        simpa [structuralState, zero, Silean.SignalMap.set] using selectedOp1Value
      · change hierStep.childOutputs .updatedFields .reg_op2 = _
        simpa [structuralState, zero, Silean.SignalMap.set] using
          congrFun updatedFieldsValue .reg_op2
      · change hierStep.childOutputs .selectedResult .result = _
        simpa [structuralState, zero, Silean.SignalMap.set] using selectedResultValue
      · change hierStep.childOutputs .selectedShift .result = _
        simpa [structuralState, zero, Silean.SignalMap.set] using selectedShiftValue
      · change hierStep.childOutputs .updatedFields .alu_out_q = _
        simpa [structuralState, zero, Silean.SignalMap.set] using
          congrFun updatedFieldsValue .alu_out_q
    · cases field
      · change hierStep.childOutputs .updatedFields .reg_pc = _
        simpa [structuralState, zero, Silean.SignalMap.set] using
          congrFun updatedFieldsValue .reg_pc
      · change hierStep.childOutputs .updatedFields .reg_next_pc = _
        simpa [structuralState, zero, Silean.SignalMap.set] using
          congrFun updatedFieldsValue .reg_next_pc
      · change hierStep.childOutputs .selectedOp1 .result = _
        simpa [structuralState, zero, Silean.SignalMap.set] using selectedOp1Value
      · change hierStep.childOutputs .updatedFields .reg_op2 = _
        simpa [structuralState, zero, Silean.SignalMap.set] using
          congrFun updatedFieldsValue .reg_op2
      · change hierStep.childOutputs .selectedResult .result = _
        simpa [structuralState, zero, Silean.SignalMap.set] using selectedResultValue
      · change hierStep.childOutputs .selectedShift .result = _
        simpa [structuralState, zero, Silean.SignalMap.set] using selectedShiftValue
      · change hierStep.childOutputs .updatedFields .alu_out_q = _
        simpa [structuralState, zero, Silean.SignalMap.set] using
          congrFun updatedFieldsValue .alu_out_q
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (shiftNextState datapathInputs current updated) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs, structuralState_eq_shiftNextState] at equation
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

end PicoRV.Datapath.ShiftUpdate
