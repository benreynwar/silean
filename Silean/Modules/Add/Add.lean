import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Foundation.BitVector
import Silean.Modules.Constant.Constant
import Silean.Modules.FullAdder.FullAdderCertified
import Silean.Modules.VectorConcat.VectorConcatCertified
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.Add

open Silean
open Contracts.Cycle.Certification.Layer

/-! A combinational fixed-width adder. Bit-vector index zero is the
least-significant bit. The contract is ordinary binary addition and does not
describe the private ripple-carry implementation. -/

inductive Input | left | right | carryIn
deriving Enumeration

inductive Output | result | carryOut
deriving Enumeration

@[reducible] def inputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Input fun
    | .left | .right => .vector width .bit
    | .carryIn => .bit

@[reducible] def outputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Output fun
    | .result => .vector width .bit
    | .carryOut => .bit

@[reducible] def ports (width : Nat) : ModulePorts :=
  ⟨inputMap width, outputMap width⟩

/-- Low bit of the natural sum of three Boolean digits. -/
def sumBit (left right carry : Bool) : Bool :=
  Primitives.xorValue (Primitives.xorValue left right) carry

/-- High bit of the natural sum of three Boolean digits. -/
def carryBit (left right carry : Bool) : Bool :=
  (left && right) || (left && carry) || (right && carry)

/-- The mathematical result and carry bit of fixed-width binary addition. -/
def addBits : (width : Nat) → (Fin width → Bool) →
    (Fin width → Bool) → Bool → (Fin width → Bool) × Bool
  | 0, _, _, carry => (fun index => Fin.elim0 index, carry)
  | width + 1, left, right, carry =>
      let lower := addBits width
        (fun index => left index.castSucc)
        (fun index => right index.castSucc) carry
      let high := sumBit
        (left (Fin.last width)) (right (Fin.last width)) lower.2
      let carryOut := carryBit
        (left (Fin.last width)) (right (Fin.last width)) lower.2
      (Fin.lastCases high lower.1, carryOut)

@[simp] private theorem toNat_lastCases (width : Nat) (high : Bool)
    (lower : Fin width → Bool) :
    BitVector.toNat (width + 1) (Fin.lastCases high lower) =
      (if high then BitVector.cardinality width else 0) +
        BitVector.toNat width lower := by
  simp [BitVector.toNat]

theorem addBits_numeric : ∀ (width : Nat) (left right : Fin width → Bool)
    (carry : Bool),
    BitVector.toNat width (addBits width left right carry).1 +
        BitVector.cardinality width * (addBits width left right carry).2.toNat =
      BitVector.toNat width left + BitVector.toNat width right + carry.toNat
  | 0, _, _, carry => by simp [addBits, BitVector.toNat, BitVector.cardinality]
  | width + 1, left, right, carry => by
      have lower := addBits_numeric width
        (fun index => left index.castSucc)
        (fun index => right index.castSucc) carry
      have high := FullAdder.numeric_value
        (left (Fin.last width)) (right (Fin.last width))
        (addBits width (fun index => left index.castSucc)
          (fun index => right index.castSucc) carry).2
      have leftBound := BitVector.toNat_lt_cardinality width
        (fun index => left index.castSucc)
      have rightBound := BitVector.toNat_lt_cardinality width
        (fun index => right index.castSucc)
      have resultBound := BitVector.toNat_lt_cardinality width
        (addBits width (fun index => left index.castSucc)
          (fun index => right index.castSucc) carry).1
      have lowerResultEta :
          (fun index => (addBits width (fun index => left index.castSucc)
            (fun index => right index.castSucc) carry).1 index) =
          (addBits width (fun index => left index.castSucc)
            (fun index => right index.castSucc) carry).1 := rfl
      rw [BitVector.cardinality_eq_pow] at lower ⊢
      rw [BitVector.cardinality_eq_pow] at leftBound rightBound resultBound
      cases leftHigh : left (Fin.last width) <;>
        cases rightHigh : right (Fin.last width) <;>
        cases lowerCarry : (addBits width
          (fun index => left index.castSucc)
          (fun index => right index.castSucc) carry).2 <;>
        simp [addBits, BitVector.toNat, leftHigh, rightHigh, lowerCarry,
          lowerResultEta, sumBit, carryBit,
          Primitives.xorValue] at lower high ⊢ <;>
        omega

inductive Rule | apply
deriving Enumeration

def outputRule (width : Nat) :
    Contracts.Cycle.CycleOutputRule (ports width) emptySignalMap where
  readsInputs := .all (inputMap width)
  writesOutputs := .all (outputMap width)
  target inputs _ := fun
    | .result => (addBits width (inputs .left) (inputs .right) (inputs .carryIn)).1
    | .carryOut => (addBits width (inputs .left) (inputs .right) (inputs .carryIn)).2

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
      outputs .result = (addBits width (inputs .left) (inputs .right) (inputs .carryIn)).1 ∧
      outputs .carryOut = (addBits width (inputs .left) (inputs .right) (inputs .carryIn)).2 := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact ⟨congrFun equal .result, congrFun equal .carryOut⟩
  · rintro ⟨result, carry⟩
    funext output
    cases output
    · exact result
    · exact carry

theorem result_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    outputs .result = (addBits width (inputs .left) (inputs .right) (inputs .carryIn)).1 :=
  ((outputRule_holds_iff width inputs state outputs).mp (evaluates.1 .apply)).1

theorem carry_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    outputs .carryOut = (addBits width (inputs .left) (inputs .right) (inputs .carryIn)).2 :=
  ((outputRule_holds_iff width inputs state outputs).mp (evaluates.1 .apply)).2

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

private def operandSplitter (width : Nat) : Composition.SignalSplitter := .vector (width + 1) .bit
private def lowerCombiner (width : Nat) : Composition.SignalCombiner := .vector width .bit
private def highCombiner : Composition.SignalCombiner := .vector 1 .bit
private def highIndex (width : Nat) : (operandSplitter width).ports.outputs.Label :=
  Fin.last width

private inductive SuccInstance
  /-- Separates the low and high bits of the left operand. -/
  | leftSplit
  /-- Separates the low and high bits of the right operand. -/
  | rightSplit
  /-- Reassembles the low left bits for the recursive child. -/
  | lowerLeft
  /-- Reassembles the low right bits for the recursive child. -/
  | lowerRight
  /-- Adds both low subvectors and produces the carry into the high bit. -/
  | lowerAdd
  /-- Adds the two high bits and the carry from the lower recursion. -/
  | highAdder
  /-- Wraps the high result bit as a one-element vector. -/
  | highBit
  /-- Concatenates the low result with the high result bit. -/
  | concat
deriving Enumeration

@[reducible] private def succInstances (width : Nat) : InstancePorts :=
  EnumeratedMap.of SuccInstance fun
    | .leftSplit => (operandSplitter width).ports
    | .rightSplit => (operandSplitter width).ports
    | .lowerLeft => (lowerCombiner width).ports
    | .lowerRight => (lowerCombiner width).ports
    | .lowerAdd => ports width
    | .highAdder => FullAdder.ports
    | .highBit => highCombiner.ports
    | .concat => VectorConcat.ports .bit width 1

@[reducible] private def succContext (width : Nat) : EndpointContext where
  ports := ports (width + 1)
  instancePorts := succInstances width

private def succWiring (width : Nat) :
    Wiring (succContext width).ports (succContext width).instancePorts where
  moduleOutput
    | .result => (succContext width).instanceOutput .concat .result
    | .carryOut => (succContext width).instanceOutput .highAdder .carryOut
  instanceInput
    | .leftSplit, .value => (succContext width).moduleInput .left
    | .rightSplit, .value => (succContext width).moduleInput .right
    | .lowerLeft, index =>
        (succContext width).instanceOutput .leftSplit index.castSucc
    | .lowerRight, index =>
        (succContext width).instanceOutput .rightSplit index.castSucc
    | .lowerAdd, .left =>
        (succContext width).instanceOutput .lowerLeft .value
    | .lowerAdd, .right =>
        (succContext width).instanceOutput .lowerRight .value
    | .lowerAdd, .carryIn => (succContext width).moduleInput .carryIn
    | .highAdder, .left =>
        (succContext width).instanceOutput .leftSplit (highIndex width)
    | .highAdder, .right =>
        (succContext width).instanceOutput .rightSplit (highIndex width)
    | .highAdder, .carryIn =>
        (succContext width).instanceOutput .lowerAdd .carryOut
    | .highBit, _ => (succContext width).instanceOutput .highAdder .sum
    | .concat, .left =>
        (succContext width).instanceOutput .lowerAdd .result
    | .concat, .right => (succContext width).instanceOutput .highBit .value

@[reducible] private def succBody (width : Nat) : ModuleBody :=
  ⟨succContext width, succWiring width⟩

/-- An LSB-first ripple-carry hierarchy with one FullAdder per bit. -/
def moduleStructure : (width : Nat) → ModuleStructure (ports width)
  | 0 => baseModuleStructure
  | width + 1 => .composite (succBody width) fun
      | .leftSplit => (operandSplitter width).certified.moduleStructure
      | .rightSplit => (operandSplitter width).certified.moduleStructure
      | .lowerLeft => (lowerCombiner width).certified.moduleStructure
      | .lowerRight => (lowerCombiner width).certified.moduleStructure
      | .lowerAdd => moduleStructure width
      | .highAdder => FullAdder.moduleStructure
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
  | .leftSplit => (operandSplitter width).cycleContract
  | .rightSplit => (operandSplitter width).cycleContract
  | .lowerLeft => (lowerCombiner width).cycleContract
  | .lowerRight => (lowerCombiner width).cycleContract
  | .lowerAdd => cycleContract width
  | .highAdder => FullAdder.cycleContract
  | .highBit => highCombiner.cycleContract
  | .concat => VectorConcat.cycleContract .bit width 1

private abbrev leftSplitOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.leftSplit, Composition.SignalComponentRule.apply⟩
private abbrev rightSplitOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.rightSplit, Composition.SignalComponentRule.apply⟩
private abbrev lowerLeftOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.lowerLeft, Composition.SignalComponentRule.apply⟩
private abbrev lowerRightOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.lowerRight, Composition.SignalComponentRule.apply⟩
private abbrev lowerAddOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.lowerAdd, Rule.apply⟩
private abbrev highSumOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.highAdder, FullAdder.Rule.sum⟩
private abbrev highCarryOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.highAdder, FullAdder.Rule.carryOut⟩
private abbrev highBitOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.highBit, Composition.SignalComponentRule.apply⟩
private abbrev concatOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.concat, VectorConcat.Rule.apply⟩

private def succScheduleOrders (width : Nat) :
    ScheduleDerivation.RuleScheduleOrders (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) where
  output := fun
    | .apply => [leftSplitOccurrence width, lowerLeftOccurrence width,
        rightSplitOccurrence width, lowerRightOccurrence width,
        lowerAddOccurrence width, highSumOccurrence width,
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

private def leftSplitInputs (width : Nat) (inputs : (ports (width + 1)).inputs.Values) :
    (operandSplitter width).ports.inputs.Values
  | .value => inputs .left

private def rightSplitInputs (width : Nat) (inputs : (ports (width + 1)).inputs.Values) :
    (operandSplitter width).ports.inputs.Values
  | .value => inputs .right

private def lowerLeftInputs (width : Nat)
    (split : (operandSplitter width).ports.outputs.Values) :
    (lowerCombiner width).ports.inputs.Values := fun index =>
  split index.castSucc

private def lowerRightInputs (width : Nat)
    (split : (operandSplitter width).ports.outputs.Values) :
    (lowerCombiner width).ports.inputs.Values := fun index =>
  split index.castSucc

private def lowerAddInputs (width : Nat)
    (inputs : (ports (width + 1)).inputs.Values)
    (lowerLeft lowerRight : (lowerCombiner width).ports.outputs.Values) :
    (ports width).inputs.Values
  | .left => lowerLeft .value
  | .right => lowerRight .value
  | .carryIn => inputs .carryIn

private def highAdderInputs (width : Nat)
    (leftSplit rightSplit : (operandSplitter width).ports.outputs.Values)
    (lower : (ports width).outputs.Values) :
    FullAdder.ports.inputs.Values
  | .left => leftSplit (highIndex width)
  | .right => rightSplit (highIndex width)
  | .carryIn => lower .carryOut

private def highBitInputs (adder : FullAdder.ports.outputs.Values) :
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
  have leftSplitOutputs : (proposal.2 .leftSplit).outputs =
      (operandSplitter width).outputValues (leftSplitInputs width inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (operandSplitter width) _ _ _).mp
      ((childMatches .leftSplit).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (succBody width)
        (fun child => (layerChildren child).moduleStructure)
        inputs proposal.2 .leftSplit = leftSplitInputs width inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  have rightSplitOutputs : (proposal.2 .rightSplit).outputs =
      (operandSplitter width).outputValues (rightSplitInputs width inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (operandSplitter width) _ _ _).mp
      ((childMatches .rightSplit).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (succBody width)
        (fun child => (layerChildren child).moduleStructure)
        inputs proposal.2 .rightSplit = rightSplitInputs width inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  have lowerLeftOutputs : (proposal.2 .lowerLeft).outputs =
      (lowerCombiner width).outputValues
        (ProposedValues.childInputs (succBody width)
          (fun child => (layerChildren child).moduleStructure)
          inputs proposal.2 .lowerLeft) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff
      (lowerCombiner width) _ _ _).mp
      ((childMatches .lowerLeft).1.1 Composition.SignalComponentRule.apply)
  have lowerRightOutputs : (proposal.2 .lowerRight).outputs =
      (lowerCombiner width).outputValues
        (ProposedValues.childInputs (succBody width)
          (fun child => (layerChildren child).moduleStructure)
          inputs proposal.2 .lowerRight) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff
      (lowerCombiner width) _ _ _).mp
      ((childMatches .lowerRight).1.1 Composition.SignalComponentRule.apply)
  have highBitOutputs : (proposal.2 .highBit).outputs =
      highCombiner.outputValues
        (ProposedValues.childInputs (succBody width)
          (fun child => (layerChildren child).moduleStructure)
          inputs proposal.2 .highBit) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff highCombiner _ _ _).mp
      ((childMatches .highBit).1.1 Composition.SignalComponentRule.apply)

  have lowerEquation := (outputRule_holds_iff width _ (childStates .lowerAdd) _).mp
    ((childMatches .lowerAdd).1.1 Rule.apply)
  have sumEquation := FullAdder.sum_of_evaluatesTo
    (evaluates := (childMatches .highAdder).1)
  have carryEquation := FullAdder.carry_of_evaluatesTo
    (evaluates := (childMatches .highAdder).1)
  have concatEquation := (VectorConcat.outputRule_holds_iff .bit width 1
    _ (childStates .concat) _).mp ((childMatches .concat).1.1 VectorConcat.Rule.apply)

  have lowerLeftInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .lowerLeft =
        lowerLeftInputs width (proposal.2 .leftSplit).outputs := by
    funext index; rfl
  have lowerRightInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .lowerRight =
        lowerRightInputs width (proposal.2 .rightSplit).outputs := by
    funext index; rfl
  have lowerAddInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .lowerAdd =
        lowerAddInputs width inputs (proposal.2 .lowerLeft).outputs
          (proposal.2 .lowerRight).outputs := by
    funext port; cases port <;> rfl
  have highAdderInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .highAdder =
        highAdderInputs width (proposal.2 .leftSplit).outputs
          (proposal.2 .rightSplit).outputs (proposal.2 .lowerAdd).outputs := by
    funext port; cases port <;> rfl
  have highBitInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .highBit =
        highBitInputs (proposal.2 .highAdder).outputs := by
    funext index; rfl
  have concatInputsEquation : ProposedValues.childInputs (succBody width) _
      inputs proposal.2 .concat =
        concatInputs width (proposal.2 .lowerAdd).outputs
          (proposal.2 .highBit).outputs := by
    funext port; cases port <;> rfl

  rw [lowerLeftInputsEquation] at lowerLeftOutputs
  rw [lowerRightInputsEquation] at lowerRightOutputs
  rw [lowerAddInputsEquation] at lowerEquation
  rw [highAdderInputsEquation] at sumEquation carryEquation
  rw [highBitInputsEquation] at highBitOutputs
  rw [concatInputsEquation] at concatEquation

  have lowerLeftValue : (proposal.2 .lowerLeft).outputs .value =
      fun index => inputs .left index.castSucc := by
    rw [congrFun lowerLeftOutputs .value]
    funext index
    change (proposal.2 .leftSplit).outputs index.castSucc = inputs .left index.castSucc
    rw [leftSplitOutputs]
    rfl
  have lowerRightValue : (proposal.2 .lowerRight).outputs .value =
      fun index => inputs .right index.castSucc := by
    rw [congrFun lowerRightOutputs .value]
    funext index
    change (proposal.2 .rightSplit).outputs index.castSucc = inputs .right index.castSucc
    rw [rightSplitOutputs]
    rfl
  have highLeftValue : (proposal.2 .leftSplit).outputs (highIndex width) =
      inputs .left (Fin.last width) := by
    rw [leftSplitOutputs]
    rfl
  have highRightValue : (proposal.2 .rightSplit).outputs (highIndex width) =
      inputs .right (Fin.last width) := by
    rw [rightSplitOutputs]
    rfl
  have highBitValue : (proposal.2 .highBit).outputs .value =
      fun _ => (proposal.2 .highAdder).outputs .sum := by
    rw [congrFun highBitOutputs .value]
    rfl

  have lowerResultEquation := lowerEquation.1
  change (proposal.2 .lowerAdd).outputs .result =
    (addBits width ((proposal.2 .lowerLeft).outputs .value)
      ((proposal.2 .lowerRight).outputs .value) (inputs .carryIn)).1
      at lowerResultEquation
  rw [lowerLeftValue, lowerRightValue] at lowerResultEquation
  have lowerCarryEquation := lowerEquation.2
  change (proposal.2 .lowerAdd).outputs .carryOut =
    (addBits width ((proposal.2 .lowerLeft).outputs .value)
      ((proposal.2 .lowerRight).outputs .value) (inputs .carryIn)).2
      at lowerCarryEquation
  rw [lowerLeftValue, lowerRightValue] at lowerCarryEquation
  change (proposal.2 .highAdder).outputs .sum = FullAdder.sumValue
    ((proposal.2 .leftSplit).outputs (highIndex width))
    ((proposal.2 .rightSplit).outputs (highIndex width))
    ((proposal.2 .lowerAdd).outputs .carryOut) at sumEquation
  change (proposal.2 .highAdder).outputs .carryOut = FullAdder.carryValue
    ((proposal.2 .leftSplit).outputs (highIndex width))
    ((proposal.2 .rightSplit).outputs (highIndex width))
    ((proposal.2 .lowerAdd).outputs .carryOut) at carryEquation
  rw [highLeftValue, highRightValue] at sumEquation carryEquation
  rw [lowerCarryEquation] at sumEquation carryEquation
  change (proposal.2 .concat).outputs .result = VectorConcat.concat
    ((proposal.2 .lowerAdd).outputs .result)
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
      change VectorConcat.concat ((proposal.2 .lowerAdd).outputs .result)
          (fun _ => (proposal.2 .highAdder).outputs .sum) = _
      rw [lowerResultEquation, sumEquation]
      exact concat_single_eq_lastCases _ _
    · change proposal.fst .carryOut = _
      rw [boundary .carryOut]
      change (proposal.2 .highAdder).outputs .carryOut = _
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
  | .leftSplit => (operandSplitter width).certified.certifiedStructure
  | .rightSplit => (operandSplitter width).certified.certifiedStructure
  | .lowerLeft => (lowerCombiner width).certified.certifiedStructure
  | .lowerRight => (lowerCombiner width).certified.certifiedStructure
  | .lowerAdd => previous.certified.certifiedStructure
  | .highAdder => FullAdder.certified.certifiedStructure
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

noncomputable opaque certification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width) :=
  implementation width

noncomputable def certified (width : Nat) : Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (certification width).bundle

@[simp] theorem certified_moduleStructure (width : Nat) :
    (certified width).moduleStructure = moduleStructure width := rfl

@[simp] theorem certified_cycleContract (width : Nat) :
    (certified width).cycleContract = cycleContract width := rfl

/-- The result and carry-out encode the full natural-number sum. -/
theorem numeric_value_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    BitVector.toNat width (outputs .result) +
        2 ^ width * (outputs .carryOut).toNat =
      BitVector.toNat width (inputs .left) +
        BitVector.toNat width (inputs .right) + (inputs .carryIn).toNat := by
  have equations := (outputRule_holds_iff width inputs state outputs).mp
    (evaluates.1 .apply)
  rw [equations.1, equations.2, ← BitVector.cardinality_eq_pow]
  exact addBits_numeric width (inputs .left) (inputs .right) (inputs .carryIn)

end Silean.Modules.Add

namespace Silean.Modules.Add.Naming

open Silean Silean.Naming

def ports (width : Nat) : ModulePortsNaming (Modules.Add.ports width) where
  inputs := ⟨fun | .left => "left" | .right => "right" | .carryIn => "carry_in"⟩
  outputs := ⟨fun | .result => "result" | .carryOut => "carry_out"⟩
  inputTypes := fun | .left | .right => .vector .bit | .carryIn => .bit
  outputTypes := fun | .result => .vector .bit | .carryOut => .bit

def naming : (width : Nat) → ModuleNaming (Modules.Add.moduleStructure width)
  | 0 => by
      rw [Modules.Add.moduleStructure.eq_def]
      exact .composite ⟨"add", "base", []⟩ (ports 0)
        (fun | Modules.Add.BaseInstance.empty => "empty")
        (fun
          | Modules.Add.BaseInstance.empty =>
              Modules.Constant.Naming.naming (.vector 0 .bit) Modules.Add.emptyValue)
  | width + 1 => by
      rw [Modules.Add.moduleStructure.eq_def]
      exact .composite
        ⟨"add", "ripple", [.natural (width + 1)]⟩
        (ports (width + 1))
        (fun
          | .leftSplit => "left_split"
          | .rightSplit => "right_split"
          | .lowerLeft => "left_lower_bits"
          | .lowerRight => "right_lower_bits"
          | .lowerAdd => "add_lower"
          | .highAdder => "add_high_bit"
          | .highBit => "high_bit"
          | .concat => "concat")
        (fun
          | .leftSplit | .rightSplit =>
              Silean.Naming.SignalAdapter.splitter (Modules.Add.operandSplitter width)
          | .lowerLeft =>
              Silean.Naming.SignalAdapter.combiner (Modules.Add.lowerCombiner width)
          | .lowerRight =>
              Silean.Naming.SignalAdapter.combiner (Modules.Add.lowerCombiner width)
          | .lowerAdd => naming width
          | .highAdder => FullAdder.design.naming
          | .highBit => Silean.Naming.SignalAdapter.combiner Modules.Add.highCombiner
          | .concat => VectorConcat.naming .bit width 1)

end Silean.Modules.Add.Naming

namespace Silean.Modules.Add

@[reducible] def design (width : Nat) : Silean.Naming.NamedModule where
  ports := ports width
  moduleStructure := moduleStructure width
  naming := Naming.naming width

end Silean.Modules.Add
