import Silean.Foundation.BitVector
import Silean.Modules.Constant.Constant
import Silean.Modules.FullAdder.FullAdder
import Silean.Modules.VectorConcat.VectorConcat
import Silean.Naming.SignalAdapterNaming
import Silean.Authoring.CircuitDescription

namespace Silean.Modules.Add

open Silean

/-! # Fixed-width addition

This is a combinational adder for LSB-first bit vectors. Its contract states
ordinary binary addition independently of the recursive ripple-carry hardware
shown below. The schedules and inductive certification are in
`Internal/AddVerification.lean`; supported structural guarantees are in
`AddTheorems.lean`.

The hierarchy changes recursively with `width`: the successor case contains
the complete lower-width adder plus one full adder. Ordinary Lean recursion is
therefore the primary hardware definition; a fixed `CircuitDescription`
version would only duplicate that programmatic construction. -/

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

private theorem sumBit_add_twice_carryBit (left right carry : Bool) :
    (sumBit left right carry).toNat + 2 * (carryBit left right carry).toNat =
      left.toNat + right.toNat + carry.toNat := by
  cases left <;> cases right <;> cases carry <;> decide

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
      have high := sumBit_add_twice_carryBit
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

/-- The observable result and carry of fixed-width addition. -/
structure Behavior (width : Nat) (inputs : (ports width).inputs.Values)
    (outputs : (ports width).outputs.Values) : Prop where
  result : outputs .result =
    (addBits width (inputs .left) (inputs .right) (inputs .carryIn)).1
  carryOut : outputs .carryOut =
    (addBits width (inputs .left) (inputs .right) (inputs .carryIn)).2

namespace Behavior

/-- An allowed contract step has the adder's complete observable behavior. -/
theorem of_allowed (width : Nat) {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step) :
    Behavior width step.inputs step.outputs := by
  rcases (outputRule_holds_iff width step.inputs step.currentState
    step.outputs).mp (allowed.1 .apply) with ⟨result, carryOut⟩
  exact ⟨result, carryOut⟩

/-- The result and carry-out encode the full natural-number sum. -/
theorem numeric_value {width : Nat} {inputs : (ports width).inputs.Values}
    {outputs : (ports width).outputs.Values}
    (behavior : Behavior width inputs outputs) :
    BitVector.toNat width (outputs .result) +
        2 ^ width * (outputs .carryOut).toNat =
      BitVector.toNat width (inputs .left) +
        BitVector.toNat width (inputs .right) + (inputs .carryIn).toNat := by
  rw [behavior.result, behavior.carryOut, ← BitVector.cardinality_eq_pow]
  exact addBits_numeric width (inputs .left) (inputs .right) (inputs .carryIn)

end Behavior

def emptyValue : (SignalType.vector 0 .bit).Denote :=
  fun index => Fin.elim0 index

inductive BaseInstance | empty
deriving Enumeration

@[reducible] def baseInstances : InstancePorts :=
  EnumeratedMap.of BaseInstance fun
    | .empty => Modules.Constant.ports (.vector 0 .bit)

@[reducible] def baseContext : EndpointContext where
  ports := ports 0
  instancePorts := baseInstances

def baseWiring : Wiring baseContext.ports baseContext.instancePorts where
  moduleOutput
    | .result => baseContext.instanceOutput .empty .output
    | .carryOut => baseContext.moduleInput .carryIn
  instanceInput | .empty, impossible => nomatch impossible

@[reducible] def baseBody : ModuleBody := ⟨baseContext, baseWiring⟩

def baseModuleStructure : ModuleStructure (ports 0) :=
  .composite baseBody fun
    | .empty => Modules.Constant.moduleStructure (.vector 0 .bit) emptyValue

def operandSplitter (width : Nat) : Composition.SignalSplitter := .vector (width + 1) .bit
def lowerCombiner (width : Nat) : Composition.SignalCombiner := .vector width .bit
def highCombiner : Composition.SignalCombiner := .vector 1 .bit
def highIndex (width : Nat) : (operandSplitter width).ports.outputs.Label :=
  Fin.last width

inductive SuccInstance
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

@[reducible] def succInstances (width : Nat) : InstancePorts :=
  EnumeratedMap.of SuccInstance fun
    | .leftSplit => (operandSplitter width).ports
    | .rightSplit => (operandSplitter width).ports
    | .lowerLeft => (lowerCombiner width).ports
    | .lowerRight => (lowerCombiner width).ports
    | .lowerAdd => ports width
    | .highAdder => FullAdder.ports
    | .highBit => highCombiner.ports
    | .concat => VectorConcat.ports .bit width 1

@[reducible] def succContext (width : Nat) : EndpointContext where
  ports := ports (width + 1)
  instancePorts := succInstances width

def succWiring (width : Nat) :
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

@[reducible] def succBody (width : Nat) : ModuleBody :=
  ⟨succContext width, succWiring width⟩

/-- An LSB-first ripple-carry hierarchy with one FullAdder per bit. -/
def moduleStructure : (width : Nat) → ModuleStructure (ports width)
  | 0 => baseModuleStructure
  | width + 1 => .composite (succBody width) fun
      | .leftSplit => .splitter (operandSplitter width)
      | .rightSplit => .splitter (operandSplitter width)
      | .lowerLeft => .combiner (lowerCombiner width)
      | .lowerRight => .combiner (lowerCombiner width)
      | .lowerAdd => moduleStructure width
      | .highAdder => FullAdder.moduleStructure
      | .highBit => .combiner highCombiner
      | .concat => VectorConcat.moduleStructure .bit width 1


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

/-- The recursive ripple implementation retains the adder's declared boundary
naming at every width. -/
theorem naming_ports (width : Nat) : (naming width).ports = ports width := by
  cases width with
  | zero =>
      rw [naming.eq_1]
      erw [ModuleNaming.ports_mpr_of_eq (by
        rw [Modules.Add.moduleStructure.eq_def])]
      rfl
  | succ width =>
      rw [naming.eq_2]
      erw [ModuleNaming.ports_mpr_of_eq (by
        rw [Modules.Add.moduleStructure.eq_def])]
      rfl

/-- The emitted boundary names of every fixed-width adder are collision-free. -/
theorem portNames_nodup (width : Nat) :
    (naming width).ports.names.Nodup := by
  rw [naming_ports]
  exact of_decide_eq_true rfl

end Silean.Modules.Add.Naming

namespace Silean.Modules.Add

@[reducible] def design (width : Nat) : Silean.Naming.NamedModule where
  ports := ports width
  moduleStructure := moduleStructure width
  naming := Naming.naming width

/-! ## Placement -/

open Silean.Authoring.CircuitDescription

/-- The result vector and carry bit produced by a placed adder. -/
structure PlacedOutputs (width : Nat) where
  result : Net (.vector width .bit)
  carryOut : Net .bit

/-- Place a fixed-width adder under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (left right : Net (.vector width .bit)) (carryIn : Net .bit) :
    Builder (PlacedOutputs width) := do
  let child ← Authoring.CircuitDescription.placeNamed name (design width) fun
    | .left => left
    | .right => right
    | .carryIn => carryIn
  pure { result := child .result, carryOut := child .carryOut }

/-- Place a fixed-width adder using the next conventional indexed name. -/
noncomputable def place (left right : Net (.vector width .bit))
    (carryIn : Net .bit) : Builder (PlacedOutputs width) := do
  let child ← placeIndexed "add" (design width) fun
    | .left => left
    | .right => right
    | .carryIn => carryIn
  pure { result := child .result, carryOut := child .carryOut }

attribute [circuit_description] placeNamed place

end Silean.Modules.Add
