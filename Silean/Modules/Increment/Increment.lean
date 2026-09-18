import Silean.Authoring.CircuitDescription
import Silean.Foundation.BitVector
import Silean.Modules.Constant.Constant
import Silean.Modules.HalfAdder.HalfAdder
import Silean.Modules.VectorConcat.VectorConcat
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.Increment

open Silean

/-! # Fixed-width increment

This wrapping combinational incrementer operates on LSB-first bit vectors. The
mathematical contract and recursive ripple hardware remain visible here;
schedules and inductive certification are in
`Internal/IncrementVerification.lean`, and supported structural guarantees are
in `IncrementTheorems.lean`. -/

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
def addCarry : (width : Nat) → (Fin width → Bool) → Bool →
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

/-- An allowed incrementer step returns the mathematical incremented value. -/
theorem result_of_allowed (width : Nat) {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step) :
    step.outputs .result = incrementValue width (step.inputs .value) :=
  (outputRule_holds_iff width step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

theorem result_toNat_of_holds (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values)
    (holds : (outputRule width).Holds inputs state outputs) :
    BitVector.toNat width (outputs .result) =
      (BitVector.toNat width (inputs .value) + 1) % BitVector.cardinality width := by
  rw [(outputRule_holds_iff width inputs state outputs).mp holds]
  exact incrementValue_toNat width (inputs .value)

/-- Numerically, an allowed step adds one modulo the vector width. -/
theorem result_toNat_of_allowed (width : Nat)
    {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step) :
    BitVector.toNat width (step.outputs .result) =
      (BitVector.toNat width (step.inputs .value) + 1) %
        BitVector.cardinality width := by
  exact result_toNat_of_holds width step.inputs step.currentState step.outputs
    (allowed.1 .apply)

/-! `Ripple` is the implementation-only recursive component used by Increment. It
adds an explicit carry input and returns both the vector result and carry out.
The public Increment module below fixes that input to true and hides carry out. -/
namespace Ripple

inductive Input | value | carryIn
deriving Enumeration

inductive Output | result | carryOut
deriving Enumeration

@[reducible] def inputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Input fun
    | .value => .vector width .bit
    | .carryIn => .bit

@[reducible] def outputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Output fun
    | .result => .vector width .bit
    | .carryOut => .bit

@[reducible] def ports (width : Nat) : ModulePorts :=
  ⟨inputMap width, outputMap width⟩

inductive Rule | apply
deriving Enumeration

def outputRule (width : Nat) :
    Contracts.Cycle.CycleOutputRule (ports width) emptySignalMap where
  readsInputs := .all (inputMap width)
  writesOutputs := .all (outputMap width)
  target inputs _ := fun
    | .result => (addCarry width (inputs .value) (inputs .carryIn)).1
    | .carryOut => (addCarry width (inputs .value) (inputs .carryIn)).2

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

def splitter (width : Nat) : Composition.SignalSplitter := .vector (width + 1) .bit
def lowerCombiner (width : Nat) : Composition.SignalCombiner := .vector width .bit
def highCombiner : Composition.SignalCombiner := .vector 1 .bit
def highIndex (width : Nat) : (splitter width).ports.outputs.Label :=
  Fin.last width

inductive SuccInstance
  | split
  | lowerBits
  | lowerRipple
  | highAdder
  | highBit
  | concat
deriving Enumeration

@[reducible] def succInstances (width : Nat) : InstancePorts :=
  EnumeratedMap.of SuccInstance fun
    | .split => (splitter width).ports
    | .lowerBits => (lowerCombiner width).ports
    | .lowerRipple => ports width
    | .highAdder => HalfAdder.ports
    | .highBit => highCombiner.ports
    | .concat => VectorConcat.ports .bit width 1

@[reducible] def succContext (width : Nat) : EndpointContext where
  ports := ports (width + 1)
  instancePorts := succInstances width

def succWiring (width : Nat) :
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

@[reducible] def succBody (width : Nat) : ModuleBody :=
  ⟨succContext width, succWiring width⟩

def moduleStructure : (width : Nat) → ModuleStructure (ports width)
  | 0 => baseModuleStructure
  | width + 1 => .composite (succBody width) fun
      | .split => .splitter (splitter width)
      | .lowerBits => .combiner (lowerCombiner width)
      | .lowerRipple => moduleStructure width
      | .highAdder => HalfAdder.moduleStructure
      | .highBit => .combiner highCombiner
      | .concat => VectorConcat.moduleStructure .bit width 1


end Ripple

/-! ## Public hardware structure

The public incrementer supplies a constant carry-in of one to the recursive
ripple implementation. -/

inductive Instance
  /-- Supplies the asserted carry-in. -/
  | one
  /-- Propagates that carry through the input bits. -/
  | ripple
deriving Enumeration

@[reducible] def instancePorts (width : Nat) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .one => Modules.Constant.ports .bit
    | .ripple => Ripple.ports width

@[reducible] def context (width : Nat) : EndpointContext where
  ports := ports width
  instancePorts := instancePorts width

def wiring (width : Nat) :
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

@[reducible] def body (width : Nat) : ModuleBody :=
  ⟨context width, wiring width⟩

def moduleStructure (width : Nat) : ModuleStructure (ports width) :=
  .composite (body width) fun
    | .one => Modules.Constant.moduleStructure .bit true
    | .ripple => Ripple.moduleStructure width


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

end Silean.Modules.Increment.Naming

namespace Silean.Modules.Increment

@[reducible] def design (width : Nat) : Silean.Naming.NamedModule where
  ports := ports width
  moduleStructure := moduleStructure width
  naming := Naming.naming width

open Silean.Authoring.CircuitDescription

/-! ## Placement -/

/-- Place an incrementer under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (value : Net (.vector width .bit)) : Builder (Net (.vector width .bit)) := do
  let child ← Authoring.CircuitDescription.placeNamed name (design width) fun
    | .value => value
  pure (child .result)

/-- Place an incrementer using the next conventional indexed name. -/
noncomputable def place (value : Net (.vector width .bit)) :
    Builder (Net (.vector width .bit)) := do
  let child ← placeIndexed "increment" (design width) fun
    | .value => value
  pure (child .result)

end Silean.Modules.Increment
