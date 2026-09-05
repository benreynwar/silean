import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Foundation.BitVector
import Silean.Modules.Constant
import Silean.Modules.HalfAdder.HalfAdderCertified
import Silean.Modules.VectorConcat.VectorConcatCertified
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.Increment

open Silean
open Contracts.Cycle.Certification.Layer

/-! A wrapping combinational incrementer for an LSB-first vector of bits. -/

inductive Input | value
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Input fun | .value => .vector width .bit

@[reducible] def outputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Output fun | .result => .vector width .bit

@[reducible] def ports (width : Nat) : ModulePorts :=
  ⟨inputMap width, outputMap width⟩

/-! Add one carry bit to an LSB-first vector. Recursion removes the highest
indexed bit, so the recursive call computes the carry arriving from all lower
indices before the high bit is evaluated. -/
private def addCarry : (width : Nat) → (Fin width → Bool) → Bool →
    (Fin width → Bool) × Bool
  | 0, _, carry => (fun index => Fin.elim0 index, carry)
  | width + 1, bits, carry =>
      let lower := addCarry width (fun index => bits index.castSucc) carry
      let high := HalfAdder.sumValue (bits (Fin.last width)) lower.2
      let carryOut := HalfAdder.carryValue (bits (Fin.last width)) lower.2
      (Fin.lastCases high lower.1, carryOut)

def incrementValue (width : Nat) (bits : Fin width → Bool) : Fin width → Bool :=
  (addCarry width bits true).1

@[simp] private theorem toNat_lastCases (width : Nat) (high : Bool)
    (lower : Fin width → Bool) :
    BitVector.toNat (width + 1) (Fin.lastCases high lower) =
      (if high then BitVector.cardinality width else 0) +
        BitVector.toNat width lower := by
  simp [BitVector.toNat]

private theorem addCarry_numeric : ∀ (width : Nat) (bits : Fin width → Bool)
    (carry : Bool),
    BitVector.toNat width (addCarry width bits carry).1 +
        BitVector.cardinality width * (addCarry width bits carry).2.toNat =
      BitVector.toNat width bits + carry.toNat
  | 0, _, carry => by simp [addCarry, BitVector.toNat, BitVector.cardinality]
  | width + 1, bits, carry => by
      have lower := addCarry_numeric width
        (fun index => bits index.castSucc) carry
      have cardinalityPositive : 0 < BitVector.cardinality width := by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.pow_pos (by omega)
      rw [BitVector.cardinality_eq_pow] at lower cardinalityPositive ⊢
      have lowerResultEta :
          (fun index => (addCarry width
            (fun index => bits index.castSucc) carry).1 index) =
          (addCarry width (fun index => bits index.castSucc) carry).1 := rfl
      cases highValue : bits (Fin.last width) <;>
        cases lowerCarry : (addCarry width
          (fun index => bits index.castSucc) carry).2 <;>
        simp [addCarry, BitVector.toNat,
          highValue, lowerCarry, lowerResultEta,
          HalfAdder.sumValue, HalfAdder.carryValue,
          Primitives.xorValue] at lower ⊢ <;>
        omega

theorem incrementValue_toNat (width : Nat) (bits : Fin width → Bool) :
    BitVector.toNat width (incrementValue width bits) =
      (BitVector.toNat width bits + 1) % BitVector.cardinality width := by
  have equation := addCarry_numeric width bits true
  simp at equation
  have bound := BitVector.toNat_lt_cardinality width (incrementValue width bits)
  have bound' : BitVector.toNat width (addCarry width bits true).1 < 2 ^ width := by
    simpa [incrementValue, BitVector.cardinality_eq_pow] using bound
  change BitVector.toNat width (addCarry width bits true).1 = _
  rw [← equation]
  simp [Nat.mod_eq_of_lt bound']

inductive Rule | apply
deriving Enumeration

def outputRule (width : Nat) :
    Contracts.Cycle.CycleOutputRule (ports width) emptySignalMap where
  readsInputs := .all (inputMap width)
  writesOutputs := .all (outputMap width)
  target inputs _ := fun | .result => incrementValue width (inputs .value)

@[reducible] def cycleContract (width : Nat) : Contracts.Cycle.ModuleCycleContract (ports width) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => outputRule width
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .result = incrementValue width (inputs .value) := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .result
  · intro equal
    funext output
    cases output
    exact equal

theorem result_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    outputs .result = incrementValue width (inputs .value) :=
  (outputRule_holds_iff width inputs state outputs).mp (evaluates.1 .apply)

theorem result_toNat_of_holds (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values)
    (holds : (outputRule width).Holds inputs state outputs) :
    BitVector.toNat width (outputs .result) =
      (BitVector.toNat width (inputs .value) + 1) % BitVector.cardinality width := by
  rw [(outputRule_holds_iff width inputs state outputs).mp holds]
  exact incrementValue_toNat width (inputs .value)

theorem result_toNat_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    BitVector.toNat width (outputs .result) =
      (BitVector.toNat width (inputs .value) + 1) % BitVector.cardinality width := by
  exact result_toNat_of_holds width inputs state outputs (evaluates.1 .apply)

/-! `Ripple` is the implementation-only recursive component used by Increment. It
adds an explicit carry input and returns both the vector result and carry out.
The public Increment module below fixes that input to true and hides carry out. -/
namespace Ripple

private inductive Input | value | carryIn
deriving Enumeration

private inductive Output | result | carryOut
deriving Enumeration

@[reducible] private def inputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Input fun
    | .value => .vector width .bit
    | .carryIn => .bit

@[reducible] private def outputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Output fun
    | .result => .vector width .bit
    | .carryOut => .bit

@[reducible] private def ports (width : Nat) : ModulePorts :=
  ⟨inputMap width, outputMap width⟩

private inductive Rule | apply
deriving Enumeration

private def outputRule (width : Nat) :
    Contracts.Cycle.CycleOutputRule (ports width) emptySignalMap where
  readsInputs := .all (inputMap width)
  writesOutputs := .all (outputMap width)
  target inputs _ := fun
    | .result => (addCarry width (inputs .value) (inputs .carryIn)).1
    | .carryOut => (addCarry width (inputs .value) (inputs .carryIn)).2

@[reducible] private def cycleContract (width : Nat) : Contracts.Cycle.ModuleCycleContract (ports width) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => outputRule width
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] private theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .result = (addCarry width (inputs .value) (inputs .carryIn)).1 ∧
      outputs .carryOut = (addCarry width (inputs .value) (inputs .carryIn)).2 := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact ⟨congrFun equal .result, congrFun equal .carryOut⟩
  · rintro ⟨result, carryOut⟩
    funext output
    cases output <;> assumption

private def emptyValue : (SignalType.vector 0 .bit).Denote :=
  fun index => Fin.elim0 index

private inductive BaseInstance | empty
deriving Enumeration

@[reducible] private def baseInstances : InstancePorts :=
  EnumeratedMap.of BaseInstance fun
    | .empty => Modules.Constant.ports (.vector 0 .bit)

@[reducible] private def baseContext : EndpointContext where
  ports := ports 0
  instancePorts := baseInstances

private def baseWiring : Wiring baseContext.ports baseContext.instancePorts where
  moduleOutput
    | .result => baseContext.instanceOutput .empty .output
    | .carryOut => baseContext.moduleInput .carryIn
  instanceInput | .empty, impossible => nomatch impossible

@[reducible] private def baseBody : ModuleBody := ⟨baseContext, baseWiring⟩

private def baseModuleStructure : ModuleStructure (ports 0) :=
  .composite baseBody fun
    | .empty => Modules.Constant.moduleStructure (.vector 0 .bit) emptyValue

private def splitter (width : Nat) : Composition.SignalSplitter := .vector (width + 1) .bit
private def lowerCombiner (width : Nat) : Composition.SignalCombiner := .vector width .bit
private def highCombiner : Composition.SignalCombiner := .vector 1 .bit
private def highIndex (width : Nat) : (splitter width).ports.outputs.Label :=
  Fin.last width

private inductive SuccInstance
  | split
  | lowerBits
  | lowerRipple
  | highAdder
  | highBit
  | concat
deriving Enumeration

@[reducible] private def succInstances (width : Nat) : InstancePorts :=
  EnumeratedMap.of SuccInstance fun
    | .split => (splitter width).ports
    | .lowerBits => (lowerCombiner width).ports
    | .lowerRipple => ports width
    | .highAdder => HalfAdder.ports
    | .highBit => highCombiner.ports
    | .concat => VectorConcat.ports .bit width 1

@[reducible] private def succContext (width : Nat) : EndpointContext where
  ports := ports (width + 1)
  instancePorts := succInstances width

private def succWiring (width : Nat) :
    Wiring (succContext width).ports (succContext width).instancePorts where
  moduleOutput
    | .result => (succContext width).instanceOutput .concat .result
    | .carryOut => (succContext width).instanceOutput .highAdder .carry
  instanceInput
    | .split, .value => (succContext width).moduleInput .value
    | .lowerBits, index =>
        (succContext width).instanceOutput .split index.castSucc
    | .lowerRipple, .value =>
        (succContext width).instanceOutput .lowerBits .value
    | .lowerRipple, .carryIn => (succContext width).moduleInput .carryIn
    | .highAdder, .left =>
        (succContext width).instanceOutput .split (highIndex width)
    | .highAdder, .right =>
        (succContext width).instanceOutput .lowerRipple .carryOut
    | .highBit, _ => (succContext width).instanceOutput .highAdder .sum
    | .concat, .left =>
        (succContext width).instanceOutput .lowerRipple .result
    | .concat, .right => (succContext width).instanceOutput .highBit .value

@[reducible] private def succBody (width : Nat) : ModuleBody :=
  ⟨succContext width, succWiring width⟩

private def moduleStructure : (width : Nat) → ModuleStructure (ports width)
  | 0 => baseModuleStructure
  | width + 1 => .composite (succBody width) fun
      | .split => (splitter width).certified.moduleStructure
      | .lowerBits => (lowerCombiner width).certified.moduleStructure
      | .lowerRipple => moduleStructure width
      | .highAdder => HalfAdder.moduleStructure
      | .highBit => highCombiner.certified.moduleStructure
      | .concat => VectorConcat.moduleStructure .bit width 1

private abbrev Implementation (width : Nat) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width)

private def Implementation.certified (implementation : Implementation width) :
    Contracts.Cycle.ModuleCycleCertified (ports width) := implementation.bundle

@[reducible] private def baseChildContracts : Contracts.Cycle.ChildCycleContracts baseBody
  | .empty => Modules.Constant.cycleContract (.vector 0 .bit) emptyValue

private abbrev baseOccurrence :
    Contracts.Cycle.Certification.Layer.RuleOccurrence baseBody baseChildContracts :=
  ⟨.empty, Primitives.ConstantRule.apply⟩

private def baseScheduleOrders : ScheduleDerivation.RuleScheduleOrders
    baseBody baseChildContracts (cycleContract 0) where
  output | .apply => [baseOccurrence]
  state := []

private def baseDerivedRuleSchedules : ScheduleDerivation.DerivedRuleSchedules
    baseBody baseChildContracts (cycleContract 0) := by
  derive_rule_schedules baseScheduleOrders

private abbrev baseSchedules := baseDerivedRuleSchedules.schedules

private theorem baseCoversChildren : baseSchedules.CoversChildren :=
  baseDerivedRuleSchedules.coversChildren

private theorem baseImplements
    (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
      baseBody baseChildContracts) :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure baseBody layerChildren)
    (cycleContract 0) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · funext index
      exact Fin.elim0 index
    · rw [show proposal.outputs .carryOut = inputs .carryIn by
          exact boundary .carryOut]
      rfl
  · rfl

private noncomputable opaque baseCertifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer baseBody baseChildContracts
      (cycleContract 0) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    baseSchedules baseCoversChildren (fun _ _ _ => True)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) baseImplements

private noncomputable def baseCertifiedChildren :
    Contracts.Cycle.Certification.Layer.ChildStructures baseBody baseChildContracts
  | .empty => (Modules.Constant.certified (.vector 0 .bit) emptyValue).certifiedStructure

private noncomputable def baseImplementation : Implementation 0 :=
  (baseCertifiedLayer.certify baseCertifiedChildren).transportStructure (by rfl)

@[reducible] private def succChildContracts (width : Nat) :
    Contracts.Cycle.ChildCycleContracts (succBody width)
  | .split => (splitter width).cycleContract
  | .lowerBits => (lowerCombiner width).cycleContract
  | .lowerRipple => cycleContract width
  | .highAdder => HalfAdder.cycleContract
  | .highBit => highCombiner.cycleContract
  | .concat => VectorConcat.cycleContract .bit width 1

private abbrev splitOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.split, Composition.SignalComponentRule.apply⟩
private abbrev lowerBitsOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.lowerBits, Composition.SignalComponentRule.apply⟩
private abbrev lowerRippleOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.lowerRipple, Rule.apply⟩
private abbrev highSumOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.highAdder, HalfAdder.Rule.sum⟩
private abbrev highCarryOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.highAdder, HalfAdder.Rule.carry⟩
private abbrev highBitOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.highBit, Composition.SignalComponentRule.apply⟩
private abbrev concatOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.concat, VectorConcat.Rule.apply⟩

private def succScheduleOrders (width : Nat) :
    ScheduleDerivation.RuleScheduleOrders (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) where
  output := fun
    | .apply => [splitOccurrence width, lowerBitsOccurrence width,
        lowerRippleOccurrence width, highSumOccurrence width,
        highCarryOccurrence width, highBitOccurrence width,
        concatOccurrence width]
  state := []

private def succDerivedRuleSchedules (width : Nat) :
    ScheduleDerivation.DerivedRuleSchedules (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) := by
  derive_rule_schedules (succScheduleOrders width)

private abbrev succSchedules (width : Nat) :=
  (succDerivedRuleSchedules width).schedules

private theorem succCoversChildren (width : Nat) :
    (succSchedules width).CoversChildren :=
  (succDerivedRuleSchedules width).coversChildren

private def splitInputs (width : Nat) (inputs : (ports (width + 1)).inputs.Values) :
    (splitter width).ports.inputs.Values
  | .value => inputs .value

private def lowerBitsInputs (width : Nat)
    (split : (splitter width).ports.outputs.Values) :
    (lowerCombiner width).ports.inputs.Values := fun index =>
  split index.castSucc

private def lowerRippleInputs (width : Nat)
    (inputs : (ports (width + 1)).inputs.Values)
    (lowerBits : (lowerCombiner width).ports.outputs.Values) :
    (ports width).inputs.Values
  | .value => lowerBits .value
  | .carryIn => inputs .carryIn

private def highAdderInputs (width : Nat)
    (split : (splitter width).ports.outputs.Values)
    (lower : (ports width).outputs.Values) :
    HalfAdder.ports.inputs.Values
  | .left => split (highIndex width)
  | .right => lower .carryOut

private def highBitInputs (adder : HalfAdder.ports.outputs.Values) :
    highCombiner.ports.inputs.Values := fun _ => adder .sum

private def concatInputs (width : Nat)
    (lower : (ports width).outputs.Values)
    (highBit : highCombiner.ports.outputs.Values) :
    (VectorConcat.ports .bit width 1).inputs.Values
  | .left => lower .result
  | .right => highBit .value

private theorem concat_single_eq_lastCases (lower : Fin width → Bool) (high : Bool) :
    VectorConcat.concat lower (fun _ : Fin 1 => high) =
      Fin.lastCases high lower := by
  funext index
  refine Fin.lastCases ?_ (fun lowerIndex => ?_) index
  · have left : VectorConcat.concat lower (fun _ : Fin 1 => high)
        (Fin.last width) = high := by
      rw [show Fin.last width = Fin.natAdd width (0 : Fin 1) by
        apply Fin.ext; simp]
      exact VectorConcat.concat_right lower (fun _ : Fin 1 => high) 0
    simpa using left
  · have left : VectorConcat.concat lower (fun _ : Fin 1 => high)
        lowerIndex.castSucc = lower lowerIndex := by
      rw [show lowerIndex.castSucc = Fin.castAdd 1 lowerIndex by
        apply Fin.ext; rfl]
      exact VectorConcat.concat_left lower (fun _ : Fin 1 => high) lowerIndex
    simpa using left

private theorem succImplements (width : Nat)
    (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
      (succBody width) (succChildContracts width)) :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure (succBody width) layerChildren)
      (cycleContract (width + 1))
      (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  have childStates : ∀ child, (succChildContracts width child).state.Values := by
    intro child
    cases child <;> exact SignalMap.emptyValues
  have childStateSubsingleton : ∀ child,
      Subsingleton (succChildContracts width child).state.Values := by
    intro child
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatches :=
    Contracts.Cycle.Certification.Layer.childSolutionsMatchContracts_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies childStates childStateSubsingleton
  have splitOutputs : (proposal.2 .split).outputs =
      (splitter width).outputValues (splitInputs width inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (splitter width) _ _ _).mp
      ((childMatches .split).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (succBody width)
        (fun child => (layerChildren child).moduleStructure)
        inputs proposal.2 .split = splitInputs width inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  have lowerBitsOutputs : (proposal.2 .lowerBits).outputs =
      (lowerCombiner width).outputValues
        (ProposedValues.childInputs (succBody width)
          (fun child => (layerChildren child).moduleStructure)
          inputs proposal.2 .lowerBits) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff
      (lowerCombiner width) _ _ _).mp
      ((childMatches .lowerBits).1.1 Composition.SignalComponentRule.apply)
  have highBitOutputs : (proposal.2 .highBit).outputs =
      highCombiner.outputValues
        (ProposedValues.childInputs (succBody width)
          (fun child => (layerChildren child).moduleStructure)
          inputs proposal.2 .highBit) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff highCombiner _ _ _).mp
      ((childMatches .highBit).1.1 Composition.SignalComponentRule.apply)

  have lowerEquation := (outputRule_holds_iff width _ (childStates .lowerRipple) _).mp
    ((childMatches .lowerRipple).1.1 Rule.apply)

  have sumEquation := HalfAdder.sum_of_evaluatesTo
    (evaluates := (childMatches .highAdder).1)
  have carryEquation := HalfAdder.carry_of_evaluatesTo
    (evaluates := (childMatches .highAdder).1)

  have concatEquation := (VectorConcat.outputRule_holds_iff .bit width 1
    _ (childStates .concat) _).mp ((childMatches .concat).1.1 VectorConcat.Rule.apply)

  have lowerBitsInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .lowerBits =
        lowerBitsInputs width (proposal.2 .split).outputs := by
    funext index; rfl
  have lowerRippleInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .lowerRipple =
        lowerRippleInputs width inputs (proposal.2 .lowerBits).outputs := by
    funext port; cases port <;> rfl
  have highAdderInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .highAdder =
        highAdderInputs width (proposal.2 .split).outputs
          (proposal.2 .lowerRipple).outputs := by
    funext port; cases port <;> rfl
  have highBitInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .highBit =
        highBitInputs (proposal.2 .highAdder).outputs := by
    funext index; rfl
  have concatInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .concat =
        concatInputs width (proposal.2 .lowerRipple).outputs
          (proposal.2 .highBit).outputs := by
    funext port; cases port <;> rfl

  rw [lowerBitsInputsEquation] at lowerBitsOutputs
  rw [lowerRippleInputsEquation] at lowerEquation
  rw [highAdderInputsEquation] at sumEquation carryEquation
  rw [highBitInputsEquation] at highBitOutputs
  rw [concatInputsEquation] at concatEquation

  have lowerValue : (proposal.2 .lowerBits).outputs .value =
      fun index => inputs .value index.castSucc := by
    rw [congrFun lowerBitsOutputs .value]
    funext index
    change (proposal.2 .split).outputs index.castSucc = inputs .value index.castSucc
    rw [splitOutputs]
    rfl
  have highValue : (proposal.2 .split).outputs (highIndex width) =
      inputs .value (Fin.last width) := by
    rw [splitOutputs]
    rfl
  have highBitValue : (proposal.2 .highBit).outputs .value =
      fun _ => (proposal.2 .highAdder).outputs .sum := by
    rw [congrFun highBitOutputs .value]
    rfl

  have lowerResultEquation := lowerEquation.1
  change (proposal.2 .lowerRipple).outputs .result =
    (addCarry width ((proposal.2 .lowerBits).outputs .value) (inputs .carryIn)).1
      at lowerResultEquation
  rw [lowerValue] at lowerResultEquation
  have lowerCarryEquation := lowerEquation.2
  change (proposal.2 .lowerRipple).outputs .carryOut =
    (addCarry width ((proposal.2 .lowerBits).outputs .value) (inputs .carryIn)).2
      at lowerCarryEquation
  rw [lowerValue] at lowerCarryEquation
  change (proposal.2 .highAdder).outputs .sum = HalfAdder.sumValue
    ((proposal.2 .split).outputs (highIndex width))
    ((proposal.2 .lowerRipple).outputs .carryOut) at sumEquation
  change (proposal.2 .highAdder).outputs .carry = HalfAdder.carryValue
    ((proposal.2 .split).outputs (highIndex width))
    ((proposal.2 .lowerRipple).outputs .carryOut) at carryEquation
  rw [highValue] at sumEquation carryEquation
  rw [lowerCarryEquation] at sumEquation carryEquation
  change (proposal.2 .concat).outputs .result = VectorConcat.concat
    ((proposal.2 .lowerRipple).outputs .result)
    ((proposal.2 .highBit).outputs .value) at concatEquation
  rw [highBitValue] at concatEquation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · rw [show proposal.outputs .result =
          (proposal.2 .concat).outputs .result by exact boundary .result]
      rw [concatEquation]
      change VectorConcat.concat ((proposal.2 .lowerRipple).outputs .result)
          (fun _ => (proposal.2 .highAdder).outputs .sum) = _
      rw [lowerResultEquation, sumEquation]
      exact concat_single_eq_lastCases _ _
    · change proposal.fst .carryOut = _
      rw [boundary .carryOut]
      change (proposal.2 .highAdder).outputs .carry = _
      rw [carryEquation]
      rfl
  · funext label
    exact nomatch label

private noncomputable opaque succCertifiedLayer (width : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (succSchedules width) (succCoversChildren width) (fun _ _ _ => True)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) (succImplements width)

private noncomputable def succCertifiedChildren (width : Nat)
    (previous : Implementation width) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (succBody width) (succChildContracts width)
  | .split => (splitter width).certified.certifiedStructure
  | .lowerBits => (lowerCombiner width).certified.certifiedStructure
  | .lowerRipple => previous.certified.certifiedStructure
  | .highAdder => HalfAdder.certified.certifiedStructure
  | .highBit => highCombiner.certified.certifiedStructure
  | .concat => (VectorConcat.certified .bit width 1).certifiedStructure

private noncomputable def succImplementation (width : Nat)
    (previous : Implementation width) : Implementation (width + 1) :=
  ((succCertifiedLayer width).certify (succCertifiedChildren width previous)).transportStructure
    (by
      unfold Contracts.Cycle.Certification.Layer.moduleStructure
        succCertifiedChildren Contracts.Cycle.ModuleCycleCertified.certifiedStructure
      rw [moduleStructure.eq_def]
      congr
      funext child
      cases child <;> rfl)

private noncomputable def implementationDefinition : (width : Nat) → Implementation width
  | 0 => baseImplementation
  | width + 1 => succImplementation width (implementationDefinition width)

private noncomputable opaque implementation (width : Nat) : Implementation width :=
  implementationDefinition width

private noncomputable def certification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width) :=
  implementation width

private noncomputable def certified (width : Nat) : Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (certification width).bundle

end Ripple

/-! ## Public hardware structure

The public incrementer supplies a constant carry-in of one to the recursive
ripple implementation. -/

private inductive Instance
  /-- Supplies the asserted carry-in. -/
  | one
  /-- Propagates that carry through the input bits. -/
  | ripple
deriving Enumeration

@[reducible] private def instancePorts (width : Nat) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .one => Modules.Constant.ports .bit
    | .ripple => Ripple.ports width

@[reducible] private def context (width : Nat) : EndpointContext where
  ports := ports width
  instancePorts := instancePorts width

private def wiring (width : Nat) :
    Wiring (context width).ports (context width).instancePorts :=
  let c := context width
  { moduleOutput := fun
    -- The ripple result is the incremented vector.
    | .result => c.instanceOutput .ripple .result
    instanceInput := fun
    | .one, impossible => nomatch impossible
    -- Apply the constant one as the initial carry.
    | .ripple, .value => c.moduleInput .value
    | .ripple, .carryIn => c.instanceOutput .one .output }

@[reducible] private def body (width : Nat) : ModuleBody :=
  ⟨context width, wiring width⟩

def moduleStructure (width : Nat) : ModuleStructure (ports width) :=
  .composite (body width) fun
    | .one => Modules.Constant.moduleStructure .bit true
    | .ripple => Ripple.moduleStructure width

@[reducible] private def childContracts (width : Nat) :
    Contracts.Cycle.ChildCycleContracts (body width)
  | .one => Modules.Constant.cycleContract .bit true
  | .ripple => Ripple.cycleContract width

private abbrev oneOccurrence (width : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (body width) (childContracts width) :=
  ⟨.one, Primitives.ConstantRule.apply⟩

private abbrev rippleOccurrence (width : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence (body width) (childContracts width) :=
  ⟨.ripple, Ripple.Rule.apply⟩

private def scheduleOrders (width : Nat) : ScheduleDerivation.RuleScheduleOrders
    (body width) (childContracts width) (cycleContract width) where
  output | .apply => [oneOccurrence width, rippleOccurrence width]
  state := []

private def derivedRuleSchedules (width : Nat) :
    ScheduleDerivation.DerivedRuleSchedules
      (body width) (childContracts width) (cycleContract width) := by
  derive_rule_schedules (scheduleOrders width)

private abbrev schedules (width : Nat) :=
  (derivedRuleSchedules width).schedules

private theorem coversChildren (width : Nat) : (schedules width).CoversChildren :=
  (derivedRuleSchedules width).coversChildren

private def rippleInputs (width : Nat)
    (inputs : (ports width).inputs.Values)
    (one : (Modules.Constant.ports .bit).outputs.Values) :
    (Ripple.ports width).inputs.Values
  | .value => inputs .value
  | .carryIn => one .output

private theorem compositeImplements (width : Nat)
    (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
      (body width) (childContracts width)) :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure (body width) layerChildren)
    (cycleContract width) (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have boundary := satisfies.1
  have childStates : ∀ child, (childContracts width child).state.Values := by
    intro child
    cases child <;> exact SignalMap.emptyValues
  have childStateSubsingleton : ∀ child,
      Subsingleton (childContracts width child).state.Values := by
    intro child
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatches :=
    Contracts.Cycle.Certification.Layer.childSolutionsMatchContracts_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies childStates childStateSubsingleton
  have oneEquation := (Modules.Constant.outputRule_holds_iff .bit true
    _ (childStates .one) _).mp ((childMatches .one).1.1 Primitives.ConstantRule.apply)
  have rippleEquation :=
    (Ripple.outputRule_holds_iff width _ (childStates .ripple) _).mp
      ((childMatches .ripple).1.1 Ripple.Rule.apply)
  have rippleInputsEquation : ProposedValues.childInputs (body width) _ inputs
      proposal.2 .ripple = rippleInputs width inputs (proposal.2 .one).outputs := by
    funext port; cases port <;> rfl
  rw [rippleInputsEquation] at rippleEquation
  have resultEquation := rippleEquation.1
  change (proposal.2 .ripple).outputs .result =
    (addCarry width (inputs .value) ((proposal.2 .one).outputs .output)).1
      at resultEquation
  rw [oneEquation] at resultEquation
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    rw [show proposal.outputs .result =
        (proposal.2 .ripple).outputs .result by exact boundary .result]
    exact resultEquation
  · funext label
    exact nomatch label

private noncomputable opaque certifiedLayer (width : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (body width)
      (childContracts width) (cycleContract width) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (schedules width) (coversChildren width) (fun _ _ _ => True)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) (compositeImplements width)

@[reducible] private noncomputable def certifiedChildren (width : Nat) :
    Contracts.Cycle.Certification.Layer.ChildStructures (body width) (childContracts width)
  | .one => (Modules.Constant.certified .bit true).certifiedStructure
  | .ripple => (Ripple.certified width).certifiedStructure

noncomputable def certification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width) :=
  ((certifiedLayer width).certify (certifiedChildren width)).transportStructure (by
    unfold Contracts.Cycle.Certification.Layer.moduleStructure
      certifiedChildren Contracts.Cycle.ModuleCycleCertified.certifiedStructure
    unfold moduleStructure
    congr
    funext child
    cases child <;> rfl)

noncomputable def certified (width : Nat) : Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (certification width).bundle

end Silean.Modules.Increment

namespace Silean.Modules.Increment.Ripple.Naming

open Silean Silean.Naming

private def ports (width : Nat) : ModulePortsNaming (Ripple.ports width) where
  inputs := ⟨fun | .value => "value" | .carryIn => "carry_in"⟩
  outputs := ⟨fun | .result => "result" | .carryOut => "carry_out"⟩
  inputTypes := fun | .value => .vector .bit | .carryIn => .bit
  outputTypes := fun | .result => .vector .bit | .carryOut => .bit

private def naming : (width : Nat) → ModuleNaming (Ripple.moduleStructure width)
  | 0 => by
      rw [Ripple.moduleStructure.eq_def]
      exact .composite ⟨"increment_ripple", "base", []⟩ (ports 0)
        (fun | Ripple.BaseInstance.empty => "empty")
        (fun
          | Ripple.BaseInstance.empty =>
              Modules.Constant.Naming.naming (.vector 0 .bit) Ripple.emptyValue)
  | width + 1 => by
      rw [Ripple.moduleStructure.eq_def]
      exact .composite
        ⟨"increment_ripple", "recursive", [.natural (width + 1)]⟩
        (ports (width + 1))
        (fun
          | .split => "split"
          | .lowerBits => "lower_bits"
          | .lowerRipple => "increment_lower"
          | .highAdder => "add_high"
          | .highBit => "high_bit"
          | .concat => "concat")
        (fun
          | .split => Silean.Naming.SignalAdapter.splitter (Ripple.splitter width)
          | .lowerBits =>
              Silean.Naming.SignalAdapter.combiner (Ripple.lowerCombiner width)
          | .lowerRipple => naming width
          | .highAdder => HalfAdder.design.naming
          | .highBit => Silean.Naming.SignalAdapter.combiner Ripple.highCombiner
          | .concat => VectorConcat.naming .bit width 1)

end Silean.Modules.Increment.Ripple.Naming

namespace Silean.Modules.Increment.Naming

open Silean Silean.Naming

def ports (width : Nat) : ModulePortsNaming (Modules.Increment.ports width) where
  inputs := ⟨fun | .value => "value"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .value => .vector .bit
  outputTypes := fun | .result => .vector .bit

def naming (width : Nat) : ModuleNaming (Modules.Increment.moduleStructure width) := by
  unfold Modules.Increment.moduleStructure
  exact .composite ⟨"increment", "structural", [.natural width]⟩ (ports width)
    (fun | Modules.Increment.Instance.one => "one"
         | Modules.Increment.Instance.ripple => "ripple")
    (fun
      | Modules.Increment.Instance.one => Modules.Constant.Naming.naming .bit true
      | Modules.Increment.Instance.ripple => Ripple.Naming.naming width)

def namedModule (width : Nat) : NamedModule where
  ports := Modules.Increment.ports width
  moduleStructure := Modules.Increment.moduleStructure width
  naming := naming width

end Silean.Modules.Increment.Naming

namespace Silean.Modules.Increment

@[reducible] def design (width : Nat) : Silean.Naming.NamedModule :=
  Naming.namedModule width

end Silean.Modules.Increment
