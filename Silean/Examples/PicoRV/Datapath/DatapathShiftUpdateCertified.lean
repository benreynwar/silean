import Silean.Examples.PicoRV.Datapath.DatapathShiftUpdate
import Silean.Examples.PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.AddSub.AddSubCertified
import Silean.Modules.EqualsConstant.EqualsConstantCertified
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Modules.VectorLayout.VectorLayoutCertified
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Datapath.ShiftUpdate

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  amountBits := amountSplitter.certified.certification,
  amountHigh23 := Primitives.orCertified.certification,
  amountGeFour := Primitives.orCertified.certification,
  amountZero := Modules.EqualsConstant.certification (.vector 5 .bit)
    (fiveBitsOfNat 0),
  leftSelect := Primitives.orCertified.certification,
  logicalSelect := Primitives.orCertified.certification,
  arithmeticSelect := Primitives.orCertified.certification,
  trueBit := Modules.Constant.certification .bit true,
  leftOne := Modules.VectorLayout.certification 32 32 (leftLayout 1),
  leftFour := Modules.VectorLayout.certification 32 32 (leftLayout 4),
  logicalOne := Modules.VectorLayout.certification 32 32 (rightLogicalLayout 1),
  logicalFour := Modules.VectorLayout.certification 32 32 (rightLogicalLayout 4),
  arithmeticOne := Modules.VectorLayout.certification 32 32
    (rightArithmeticLayout 1),
  arithmeticFour := Modules.VectorLayout.certification 32 32
    (rightArithmeticLayout 4),
  selectedLeft := Modules.Mux.certification (.vector 32 .bit),
  selectedLogical := Modules.Mux.certification (.vector 32 .bit),
  selectedArithmetic := Modules.Mux.certification (.vector 32 .bit),
  selectArithmetic := Modules.Mux.certification (.vector 32 .bit),
  selectLogical := Modules.Mux.certification (.vector 32 .bit),
  selectLeft := Modules.Mux.certification (.vector 32 .bit),
  one := Modules.Constant.certification (.vector 5 .bit) (fiveBitsOfNat 1),
  four := Modules.Constant.certification (.vector 5 .bit) (fiveBitsOfNat 4),
  selectedStep := Modules.Mux.certification (.vector 5 .bit),
  subtractStep := Modules.AddSub.certification 5,
  selectedOp1 := Modules.Mux.certification (.vector 32 .bit),
  selectedShift := Modules.Mux.certification (.vector 5 .bit),
  selectedResult := Modules.Mux.certification (.vector 32 .bit),
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Modules.NamedTupleSplitter.Rule.apply,
    .amountBits => Composition.SignalComponentRule.apply,
    {.amountHigh23, .amountGeFour, .leftSelect, .logicalSelect,
      .arithmeticSelect} => Primitives.OrRule.apply,
    .amountZero => Modules.EqualsConstant.Rule.apply,
    {.trueBit, .one, .four} => Primitives.ConstantRule.apply,
    {.leftOne, .leftFour, .logicalOne, .logicalFour,
      .arithmeticOne, .arithmeticFour} => Modules.VectorLayout.Rule.apply,
    {.selectedLeft, .selectedLogical, .selectedArithmetic, .selectArithmetic,
      .selectLogical, .selectLeft, .selectedStep} => Modules.Mux.Rule.select,
    .subtractStep => Modules.AddSub.Rule.apply,
    {.selectedOp1, .selectedShift, .selectedResult} => Modules.Mux.Rule.select,
    .result => Modules.NamedTupleCombiner.Rule.apply]
  state := []

theorem left_layout (word : Word) (amount : Nat) :
    Modules.VectorLayout.apply (leftLayout amount) word = shiftLeft word amount := by
  funext index
  by_cases low : index.val < amount <;>
    simp [Modules.VectorLayout.apply, leftLayout, shiftLeft, low]

theorem logical_layout (word : Word) (amount : Nat) :
    Modules.VectorLayout.apply (rightLogicalLayout amount) word =
      shiftRightLogical word amount := by
  funext index
  by_cases high : index.val + amount < 32 <;>
    simp [Modules.VectorLayout.apply, rightLogicalLayout, shiftRightLogical, high]

theorem arithmetic_layout (word : Word) (amount : Nat) :
    Modules.VectorLayout.apply (rightArithmeticLayout amount) word =
      shiftRightArithmetic word amount := by
  funext index
  by_cases high : index.val + amount < 32 <;>
    simp [Modules.VectorLayout.apply, rightArithmeticLayout,
      shiftRightArithmetic, high]

private theorem high_bits_mean_ge_four : ∀ bits : FiveBits,
    (bits 2 || bits 3 || bits 4) = decide (BitVector.toNat 5 bits ≥ 4) := by
  intro bits
  have lowBound := BitVector.toNat_lt_cardinality 2
    (fun index => bits index.castSucc.castSucc.castSucc)
  cases bit4 : bits 4 <;> cases bit3 : bits 3 <;> cases bit2 : bits 2 <;>
    simp [BitVector.toNat, BitVector.cardinality, bit4, bit3, bit2] at lowBound ⊢ <;>
    omega

private theorem signal_equal_zero : ∀ bits : FiveBits,
    (SignalType.vector 5 .bit).equal bits (fiveBitsOfNat 0) =
      decide (BitVector.toNat 5 bits = 0) := by
  intro bits
  apply Bool.eq_iff_iff.mpr
  rw [SignalType.equal_eq_true_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro rfl
    simp [fiveBitsOfNat, BitVector.toNat]
  · intro zero
    apply BitVector.toNat_injective 5
    rw [zero]
    simp [fiveBitsOfNat, BitVector.toNat]

private theorem subtract_selected_step : ∀ bits : FiveBits,
    BitVector.toNat 5 bits ≠ 0 →
      (Modules.AddSub.addSubBits 5 bits
        (bif bits 2 || bits 3 || bits 4 then fiveBitsOfNat 4
          else fiveBitsOfNat 1) true).1 =
        fiveBitsOfNat (BitVector.toNat 5 bits -
          if BitVector.toNat 5 bits ≥ 4 then 4 else 1) := by
  intro bits nonzero
  apply BitVector.toNat_injective 5
  rw [Modules.AddSub.addSubBits_result_toNat]
  simp only [if_true]
  have amountBound := BitVector.toNat_lt_cardinality 5 bits
  have highMeaning := high_bits_mean_ge_four bits
  cases high : bits 2 || bits 3 || bits 4
  · rw [high] at highMeaning
    have small : BitVector.toNat 5 bits < 4 := by simpa using highMeaning
    have positive : 1 ≤ BitVector.toNat 5 bits := by omega
    simp [show ¬ BitVector.toNat 5 bits ≥ 4 by omega]
    change (BitVector.toNat 5 bits + BitVector.cardinality 5 -
        BitVector.toNat 5 (fiveBitsOfNat 1)) % BitVector.cardinality 5 =
      BitVector.toNat 5 (fiveBitsOfNat (BitVector.toNat 5 bits - 1))
    rw [show fiveBitsOfNat 1 = BitVector.ofNat 5 1 by rfl,
      show fiveBitsOfNat (BitVector.toNat 5 bits - 1) =
        BitVector.ofNat 5 (BitVector.toNat 5 bits - 1) by rfl]
    rw [BitVector.toNat_ofNat, BitVector.toNat_ofNat]
    rw [show BitVector.cardinality 5 = 32 by decide] at amountBound ⊢
    have sum : BitVector.toNat 5 bits + 32 - 1 =
        (BitVector.toNat 5 bits - 1) + 32 := by omega
    rw [sum, Nat.add_mod, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt (by omega : BitVector.toNat 5 bits - 1 < 32)]
    exact Nat.mod_eq_of_lt (by omega)
  · have large : 4 ≤ BitVector.toNat 5 bits := by
      simpa [high] using highMeaning
    simp [large]
    change (BitVector.toNat 5 bits + BitVector.cardinality 5 -
        BitVector.toNat 5 (fiveBitsOfNat 4)) % BitVector.cardinality 5 =
      BitVector.toNat 5 (fiveBitsOfNat (BitVector.toNat 5 bits - 4))
    rw [show fiveBitsOfNat 4 = BitVector.ofNat 5 4 by rfl,
      show fiveBitsOfNat (BitVector.toNat 5 bits - 4) =
        BitVector.ofNat 5 (BitVector.toNat 5 bits - 4) by rfl]
    rw [BitVector.toNat_ofNat, BitVector.toNat_ofNat]
    rw [show BitVector.cardinality 5 = 32 by decide] at amountBound ⊢
    have sum : BitVector.toNat 5 bits + 32 - 4 =
        (BitVector.toNat 5 bits - 4) + 32 := by omega
    rw [sum, Nat.add_mod, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt (by omega : BitVector.toNat 5 bits - 4 < 32)]
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

  have amountSplit := (amountSplitter.outputRule_holds_iff _ _ _).mp
    ((childMatch .amountBits).1.1 Composition.SignalComponentRule.apply)
  have amountBit (index : Fin 5) :
      (proposal.2 .amountBits).outputs index = current .reg_sh index := by
    have equation := congrFun amountSplit index
    have wired : (proposal.2 .amountBits).outputs index =
        (proposal.2 .currentFields).outputs .reg_sh index := by
      simpa [Composition.SignalSplitter.outputValues, amountSplitter,
        ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using equation
    rw [wired, congrFun currentFieldsValue .reg_sh]
  have high23Value : (proposal.2 .amountHigh23).outputs .output =
      (current .reg_sh 2 || current .reg_sh 3) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .amountHigh23).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [amountBit 2, amountBit 3] at equation
    exact equation
  have geFourValue : (proposal.2 .amountGeFour).outputs .output =
      decide (shiftAmount current ≥ 4) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .amountGeFour).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [high23Value, amountBit 4] at equation
    rw [equation]
    exact high_bits_mean_ge_four (current .reg_sh)
  have zeroValue : (proposal.2 .amountZero).outputs .result =
      decide (shiftAmount current = 0) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 5 .bit) (fiveBitsOfNat 0) _ _ _).mp
      ((childMatch .amountZero).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue] at equation
    rw [equation]
    exact signal_equal_zero (current .reg_sh)

  have leftSelectValue : (proposal.2 .leftSelect).outputs .output =
      (datapathInputs.instr_slli || datapathInputs.instr_sll) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .leftSelect).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .instr_slli, inputField .instr_sll] at equation
    exact equation
  have logicalSelectValue : (proposal.2 .logicalSelect).outputs .output =
      (datapathInputs.instr_srli || datapathInputs.instr_srl) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .logicalSelect).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .instr_srli, inputField .instr_srl] at equation
    exact equation
  have arithmeticSelectValue : (proposal.2 .arithmeticSelect).outputs .output =
      (datapathInputs.instr_srai || datapathInputs.instr_sra) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .arithmeticSelect).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [inputField .instr_srai, inputField .instr_sra] at equation
    exact equation

  have leftOneValue : (proposal.2 .leftOne).outputs .output =
      shiftLeft (current .reg_op1) 1 := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 32
      (leftLayout 1) _ _ _ _ (childMatch .leftOne).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, left_layout] at equation
    exact equation
  have leftFourValue : (proposal.2 .leftFour).outputs .output =
      shiftLeft (current .reg_op1) 4 := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 32
      (leftLayout 4) _ _ _ _ (childMatch .leftFour).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, left_layout] at equation
    exact equation
  have logicalOneValue : (proposal.2 .logicalOne).outputs .output =
      shiftRightLogical (current .reg_op1) 1 := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 32
      (rightLogicalLayout 1) _ _ _ _ (childMatch .logicalOne).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, logical_layout] at equation
    exact equation
  have logicalFourValue : (proposal.2 .logicalFour).outputs .output =
      shiftRightLogical (current .reg_op1) 4 := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 32
      (rightLogicalLayout 4) _ _ _ _ (childMatch .logicalFour).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, logical_layout] at equation
    exact equation
  have arithmeticOneValue : (proposal.2 .arithmeticOne).outputs .output =
      shiftRightArithmetic (current .reg_op1) 1 := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 32
      (rightArithmeticLayout 1) _ _ _ _ (childMatch .arithmeticOne).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, arithmetic_layout] at equation
    exact equation
  have arithmeticFourValue : (proposal.2 .arithmeticFour).outputs .output =
      shiftRightArithmetic (current .reg_op1) 4 := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 32
      (rightArithmeticLayout 4) _ _ _ _ (childMatch .arithmeticFour).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, arithmetic_layout] at equation
    exact equation

  have selectedLeftValue : (proposal.2 .selectedLeft).outputs .result =
      shiftLeft (current .reg_op1) (selectedStepAmount current) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectedLeft).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [geFourValue, leftOneValue, leftFourValue] at equation
    by_cases large : shiftAmount current ≥ 4
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
  have selectedLogicalValue : (proposal.2 .selectedLogical).outputs .result =
      shiftRightLogical (current .reg_op1) (selectedStepAmount current) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectedLogical).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [geFourValue, logicalOneValue, logicalFourValue] at equation
    by_cases large : shiftAmount current ≥ 4
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
  have selectedArithmeticValue : (proposal.2 .selectedArithmetic).outputs .result =
      shiftRightArithmetic (current .reg_op1) (selectedStepAmount current) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectedArithmetic).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [geFourValue, arithmeticOneValue, arithmeticFourValue] at equation
    by_cases large : shiftAmount current ≥ 4
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
    · simp [large, selectedStepAmount] at equation ⊢
      exact equation
  have selectArithmeticValue : (proposal.2 .selectArithmetic).outputs .result =
      (if datapathInputs.instr_srai || datapathInputs.instr_sra then
        shiftRightArithmetic (current .reg_op1) (selectedStepAmount current)
      else current .reg_op1) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectArithmetic).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [arithmeticSelectValue, currentFieldsValue,
      selectedArithmeticValue] at equation
    cases arithmetic : datapathInputs.instr_srai || datapathInputs.instr_sra <;>
      simp [arithmetic] at equation ⊢ <;> exact equation
  have selectLogicalValue : (proposal.2 .selectLogical).outputs .result =
      (if datapathInputs.instr_srli || datapathInputs.instr_srl then
        shiftRightLogical (current .reg_op1) (selectedStepAmount current)
      else if datapathInputs.instr_srai || datapathInputs.instr_sra then
        shiftRightArithmetic (current .reg_op1) (selectedStepAmount current)
      else current .reg_op1) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectLogical).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [logicalSelectValue, selectedLogicalValue,
      selectArithmeticValue] at equation
    cases logical : datapathInputs.instr_srli || datapathInputs.instr_srl <;>
      simp [logical] at equation ⊢ <;> exact equation
  have shiftedValueEquation : (proposal.2 .selectLeft).outputs .result =
      shiftedStep datapathInputs current := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectLeft).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [leftSelectValue, selectedLeftValue, selectLogicalValue] at equation
    cases left : datapathInputs.instr_slli || datapathInputs.instr_sll <;>
      cases logical : datapathInputs.instr_srli || datapathInputs.instr_srl <;>
      cases arithmetic : datapathInputs.instr_srai || datapathInputs.instr_sra <;>
      simp [shiftedStep, shiftedValue, left, logical, arithmetic] at equation ⊢ <;>
      exact equation

  have trueValue := (Modules.Constant.outputRule_holds_iff .bit true _ _ _).mp
    ((childMatch .trueBit).1.1 Primitives.ConstantRule.apply)
  have oneValue := (Modules.Constant.outputRule_holds_iff
    (.vector 5 .bit) (fiveBitsOfNat 1) _ _ _).mp
    ((childMatch .one).1.1 Primitives.ConstantRule.apply)
  have fourValue := (Modules.Constant.outputRule_holds_iff
    (.vector 5 .bit) (fiveBitsOfNat 4) _ _ _).mp
    ((childMatch .four).1.1 Primitives.ConstantRule.apply)
  have stepValue : (proposal.2 .selectedStep).outputs .result =
      (if shiftAmount current ≥ 4 then fiveBitsOfNat 4 else fiveBitsOfNat 1) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 5 .bit)
      _ _ _ _ (childMatch .selectedStep).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [geFourValue, oneValue, fourValue] at equation
    by_cases large : shiftAmount current ≥ 4
    · simp [large] at equation ⊢
      exact equation
    · simp [large] at equation ⊢
      exact equation
  have subtractValue : (proposal.2 .subtractStep).outputs .result =
      (Modules.AddSub.addSubBits 5 (current .reg_sh)
        (bif current .reg_sh 2 || current .reg_sh 3 || current .reg_sh 4 then
          fiveBitsOfNat 4 else fiveBitsOfNat 1) true).1 := by
    have equation := Modules.AddSub.result_of_evaluatesTo 5
      _ _ _ _ (childMatch .subtractStep).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, stepValue, trueValue] at equation
    have highMeaning := high_bits_mean_ge_four (current .reg_sh)
    cases high : current .reg_sh 2 || current .reg_sh 3 || current .reg_sh 4
    · have small : ¬ shiftAmount current ≥ 4 := by
        simpa [shiftAmount, high] using highMeaning
      simpa [high, small] using equation
    · have large : shiftAmount current ≥ 4 := by
        simpa [shiftAmount, high] using highMeaning
      simpa [high, large] using equation

  have selectedOp1Value : (proposal.2 .selectedOp1).outputs .result =
      (if shiftAmount current = 0 then updated .reg_op1
      else shiftedStep datapathInputs current) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectedOp1).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [zeroValue, shiftedValueEquation, updatedFieldsValue] at equation
    by_cases zero : shiftAmount current = 0
    · simp [zero] at equation ⊢
      exact equation
    · simp [zero] at equation ⊢
      exact equation
  have selectedShiftValue : (proposal.2 .selectedShift).outputs .result =
      (if shiftAmount current = 0 then updated .reg_sh
      else fiveBitsOfNat
        (shiftAmount current - selectedStepAmount current)) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 5 .bit)
      _ _ _ _ (childMatch .selectedShift).1
    normalize_child_hyp equation unfolding body, wiring, context
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
  have selectedResultValue : (proposal.2 .selectedResult).outputs .result =
      (if shiftAmount current = 0 then current .reg_op1
      else updated .reg_out) := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .selectedResult).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [zeroValue, updatedFieldsValue, currentFieldsValue] at equation
    by_cases zero : shiftAmount current = 0
    · simp [zero] at equation ⊢
      exact equation
    · simp [zero] at equation ⊢
      exact equation

  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result = structuralState datapathInputs current updated := by
    funext field
    by_cases zero : shiftAmount current = 0 <;> cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, structuralState,
        zero, if_true, if_false, SignalMap.set]
    all_goals first
      | simpa [zero] using congrFun updatedFieldsValue _
      | simpa [zero] using selectedOp1Value
      | simpa [zero] using selectedShiftValue
      | simpa [zero] using selectedResultValue
  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack (shiftNextState datapathInputs current updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs, structuralState_eq_shiftNextState] at equation
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

end Silean.Examples.PicoRV.Datapath.ShiftUpdate
