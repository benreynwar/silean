import Silean.Foundation.BitVector
import Silean.Modules.Constant.Constant
import Silean.Modules.Mask.Mask
import Silean.Modules.VectorConcat.VectorConcat
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.Not

namespace Silean.Modules.BinaryToOneHot

open Silean
open Contracts.Cycle.Certification.Layer

/-! # Binary-to-one-hot decoder

For a `width`-bit input, exactly one of the `2 ^ width` output bits is asserted.
Ordinary recursion keeps the base and successor hardware cases visible here;
recursive certification is in `Internal/BinaryToOneHotVerification.lean`, and
public structural guarantees are in `BinaryToOneHotTheorems.lean`. -/

inductive Input | value
deriving Enumeration

inductive Output | result
deriving Enumeration

@[reducible] def inputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Input fun | .value => .vector width .bit

abbrev size := BitVector.cardinality

@[simp] theorem size_eq_pow (width : Nat) : size width = 2 ^ width :=
  BitVector.cardinality_eq_pow width

@[reducible] def outputMap (width : Nat) : SignalMap :=
  EnumeratedMap.of Output fun | .result => .vector (size width) .bit

@[reducible] def ports (width : Nat) : ModulePorts :=
  ⟨inputMap width, outputMap width⟩

/-! Bit index `i` has weight `2 ^ i`. The definition is deliberately
contract-level Lean code; it does not mention the structural hierarchy. -/
def decode : (width : Nat) → (Fin width → Bool) → Fin (size width) → Bool
  | 0, _ => fun _ => true
  | width + 1, bits => fun index =>
      Fin.addCases
        (fun lower => !bits (Fin.last width) &&
          decode width (fun i => bits i.castSucc) lower)
        (fun upper => bits (Fin.last width) &&
          decode width (fun i => bits i.castSucc) upper)
        index

private theorem castAdd_injective {n : Nat} (left right : Fin n) :
    Fin.castAdd n left = Fin.castAdd n right ↔ left = right := by
  constructor
  · intro equal; apply Fin.ext
    simpa [Fin.castAdd] using congrArg Fin.val equal
  · intro equal; cases equal; rfl

private theorem natAdd_injective {n : Nat} (left right : Fin n) :
    Fin.natAdd n left = Fin.natAdd n right ↔ left = right := by
  constructor
  · intro equal; apply Fin.ext
    simpa [Fin.natAdd] using congrArg Fin.val equal
  · intro equal; cases equal; rfl

private theorem castAdd_ne_natAdd {n : Nat} (left right : Fin n) :
    Fin.castAdd n left ≠ Fin.natAdd n right := by
  intro equal
  have values := congrArg Fin.val equal
  have bound := left.isLt
  simp [Fin.castAdd, Fin.natAdd] at values
  omega

private theorem addNat_eq_natAdd {n : Nat} (index : Fin n) :
    index.addNat n = Fin.natAdd n index := by
  apply Fin.ext
  simp [Fin.addNat, Fin.natAdd, Nat.add_comm]

private theorem castAdd_ne_addNat {n : Nat} (left right : Fin n) :
    Fin.castAdd n left ≠ right.addNat n := by
  rw [addNat_eq_natAdd]
  exact castAdd_ne_natAdd left right

private theorem addNat_ne_castAdd {n : Nat} (left right : Fin n) :
    left.addNat n ≠ Fin.castAdd n right :=
  Ne.symm (castAdd_ne_addNat right left)

private theorem addNat_injective {n : Nat} (left right : Fin n) :
    left.addNat n = right.addNat n ↔ left = right := by
  rw [addNat_eq_natAdd, addNat_eq_natAdd]
  exact natAdd_injective left right

private theorem addCases_addNat {n : Nat} (left right : Fin n → α)
    (index : Fin n) :
    Fin.addCases left right (index.addNat n) = right index := by
  rw [addNat_eq_natAdd]
  exact Fin.addCases_right index

theorem decode_eq_true_iff : ∀ (width : Nat) (bits : Fin width → Bool)
    (index : Fin (size width)),
    decode width bits index = true ↔ index = BitVector.toIndex width bits
  | 0, _, index => by
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ => rfl⟩
  | width + 1, bits, index => by
      refine Fin.addCases ?_ ?_ index
      · intro lower
        cases high : bits (Fin.last width) <;>
          simp [decode, BitVector.toIndex, high, decode_eq_true_iff,
            castAdd_injective, castAdd_ne_addNat]
      · intro upper
        cases high : bits (Fin.last width)
        · simp [decode, BitVector.toIndex, high, addCases_addNat,
            addNat_ne_castAdd]
        · simp [decode, BitVector.toIndex, high, decode_eq_true_iff,
            addCases_addNat, addNat_injective]

def oneHot (width : Nat) (bits : Fin width → Bool) : Fin (size width) → Bool :=
  fun index => decide (index.val = BitVector.toNat width bits)

theorem oneHot_eq_decode (width : Nat) (bits : Fin width → Bool) :
    oneHot width bits = decode width bits := by
  funext index
  apply Bool.eq_iff_iff.mpr
  rw [decode_eq_true_iff]
  simp only [oneHot, decide_eq_true_iff]
  constructor
  · intro equal
    apply Fin.ext
    simpa [BitVector.toIndex_val] using equal
  · intro equal
    simpa [BitVector.toIndex_val] using congrArg Fin.val equal

inductive Rule | apply
deriving Enumeration

def outputRule (width : Nat) :
    Contracts.Cycle.CycleOutputRule (ports width) emptySignalMap where
  readsInputs := .all (inputMap width)
  writesOutputs := .all (outputMap width)
  target inputs _ := fun | .result => oneHot width (inputs .value)

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
      outputs .result = oneHot width (inputs .value) := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .result
  · intro equal
    funext output
    cases output
    exact equal

theorem result_of_holds (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values)
    (holds : (outputRule width).Holds inputs state outputs)
    (index : Fin (size width)) :
    outputs .result index = oneHot width (inputs .value) index := by
  rw [(outputRule_holds_iff width inputs state outputs).mp holds]

theorem result_eq_true_iff_of_holds (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values)
    (holds : (outputRule width).Holds inputs state outputs)
    (index : Fin (size width)) :
    outputs .result index = true ↔
      index.val = BitVector.toNat width (inputs .value) := by
  rw [result_of_holds width inputs state outputs holds index]
  exact decide_eq_true_iff

/-! ## Hardware structure

Width zero is the one-element constant vector `[true]`. A successor width
splits off the highest-index bit, rebuilds the lower-bit vector, recursively
decodes it, masks two copies with the high bit and its inverse, then joins
the halves. -/

namespace Internal

def baseValue : (SignalType.vector 1 .bit).Denote := fun _ => true

inductive BaseInstance
  /-- Supplies the sole asserted output for a zero-width input. -/
  | constant
deriving Enumeration

@[reducible] def baseInstances : InstancePorts :=
  EnumeratedMap.of BaseInstance fun
    | .constant => Modules.Constant.ports (.vector 1 .bit)

@[reducible] def baseContext : EndpointContext where
  ports := ports 0
  instancePorts := baseInstances

def baseWiring : Wiring baseContext.ports baseContext.instancePorts where
  moduleOutput | .result => baseContext.instanceOutput .constant .output
  instanceInput | .constant, impossible => nomatch impossible

@[reducible] def baseBody : ModuleBody := ⟨baseContext, baseWiring⟩

def baseModuleStructure : ModuleStructure (ports 0) :=
  .composite baseBody fun
    | .constant => Modules.Constant.moduleStructure (.vector 1 .bit) baseValue

def splitter (width : Nat) : Composition.SignalSplitter := .vector (width + 1) .bit
def lowerCombiner (width : Nat) : Composition.SignalCombiner := .vector width .bit
def highIndex (width : Nat) : (splitter width).ports.outputs.Label :=
  Fin.last width

end Internal

open Internal

inductive SuccInstance
  /-- Exposes the individual input bits. -/
  | split
  /-- Rebuilds the lower input bits for the recursive decoder. -/
  | lowerBits
  /-- Recursively decodes the lower bits. -/
  | decode
  /-- Inverts the high bit for the lower output half. -/
  | invert
  /-- Enables the lower half when the high bit is zero. -/
  | lowerMask
  /-- Enables the upper half when the high bit is one. -/
  | upperMask
  /-- Joins the two halves into the one-hot result. -/
  | concat
deriving Enumeration

@[reducible] def succInstances (width : Nat) : InstancePorts :=
  EnumeratedMap.of SuccInstance fun
    | .split => (splitter width).ports
    | .lowerBits => (lowerCombiner width).ports
    | .decode => ports width
    | .invert => Primitives.not.ports
    | .lowerMask | .upperMask => Modules.Mask.ports (.vector (size width) .bit)
    | .concat => Modules.VectorConcat.ports .bit (size width) (size width)

@[reducible] def succContext (width : Nat) : EndpointContext where
  ports := ports (width + 1)
  instancePorts := succInstances width

def succWiring (width : Nat) :
    Wiring (succContext width).ports (succContext width).instancePorts where
  moduleOutput
    -- The concatenated masked halves form the result.
    | .result => (succContext width).instanceOutput .concat .result
  instanceInput
    -- Split the input and rebuild its lower bits.
    | .split, .value => (succContext width).moduleInput .value
    | .lowerBits, index =>
        (succContext width).instanceOutput .split index.castSucc
    | .decode, .value =>
        (succContext width).instanceOutput .lowerBits .value
    -- Use the high bit to select one copy of the recursive result.
    | .invert, .input =>
        (succContext width).instanceOutput .split (highIndex width)
    | .lowerMask, .value =>
        (succContext width).instanceOutput .decode .result
    | .lowerMask, .mask =>
        (succContext width).instanceOutput .invert .output
    | .upperMask, .value =>
        (succContext width).instanceOutput .decode .result
    | .upperMask, .mask =>
        (succContext width).instanceOutput .split (highIndex width)
    -- Join the selected lower and upper halves.
    | .concat, .left =>
        (succContext width).instanceOutput .lowerMask .result
    | .concat, .right =>
        (succContext width).instanceOutput .upperMask .result

@[reducible] def succBody (width : Nat) : ModuleBody :=
  ⟨succContext width, succWiring width⟩

def moduleStructure : (width : Nat) → ModuleStructure (ports width)
  | 0 => baseModuleStructure
  | width + 1 => .composite (succBody width) fun
      | .split => .splitter (splitter width)
      | .lowerBits => .combiner (lowerCombiner width)
      | .decode => moduleStructure width
      | .invert => Primitives.notCertified.moduleStructure
      | .lowerMask | .upperMask =>
          Modules.Mask.moduleStructure (.vector (size width) .bit)
      | .concat => Modules.VectorConcat.moduleStructure .bit (size width) (size width)


end Silean.Modules.BinaryToOneHot

namespace Silean.Modules.BinaryToOneHot.Naming

open Silean Silean.Naming

def ports (width : Nat) : ModulePortsNaming (Modules.BinaryToOneHot.ports width) where
  inputs := ⟨fun | .value => "value"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun | .value => .vector .bit
  outputTypes := fun | .result => .vector .bit

def naming : (width : Nat) →
    ModuleNaming (Modules.BinaryToOneHot.moduleStructure width)
  | 0 => by
      rw [Modules.BinaryToOneHot.moduleStructure.eq_def]
      exact .composite ⟨"binary_to_one_hot", "base", []⟩ (ports 0)
        (fun | Modules.BinaryToOneHot.Internal.BaseInstance.constant => "constant")
        (fun
          | Modules.BinaryToOneHot.Internal.BaseInstance.constant =>
              Modules.Constant.Naming.naming (SignalType.vector 1 .bit)
                Modules.BinaryToOneHot.Internal.baseValue)
  | width + 1 => by
      rw [Modules.BinaryToOneHot.moduleStructure.eq_def]
      exact .composite
        ⟨"binary_to_one_hot", "recursive", [.natural (width + 1)]⟩
        (ports (width + 1))
        (fun
          | .split => "split"
          | .lowerBits => "lower_bits"
          | .decode => "decode_lower"
          | .invert => "invert_high"
          | .lowerMask => "lower_mask"
          | .upperMask => "upper_mask"
          | .concat => "concat")
        (fun
          | .split => Silean.Naming.SignalAdapter.splitter
              (Modules.BinaryToOneHot.Internal.splitter width)
          | .lowerBits => Silean.Naming.SignalAdapter.combiner
              (Modules.BinaryToOneHot.Internal.lowerCombiner width)
          | .decode => naming width
          | .invert => Silean.Naming.Primitive.not
          | .lowerMask | .upperMask => Modules.Mask.Naming.naming
              (.vector (Modules.BinaryToOneHot.size width) .bit)
          | .concat => Modules.VectorConcat.naming .bit
              (Modules.BinaryToOneHot.size width) (Modules.BinaryToOneHot.size width))

end Silean.Modules.BinaryToOneHot.Naming

namespace Silean.Modules.BinaryToOneHot

@[reducible] def design (width : Nat) : Silean.Naming.NamedModule where
  ports := ports width
  moduleStructure := moduleStructure width
  naming := Naming.naming width

end Silean.Modules.BinaryToOneHot
