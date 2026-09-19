import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.CircuitDescription
import Silean.Authoring.CircuitLogic
import Silean.Foundation.BitVector
import Silean.Modules.Add.Add
import Silean.Modules.BitwiseXor.BitwiseXor
import Silean.Naming.SignalAdapterNaming
import Silean.Modules.AddSub.Internal.AddSubStructure

namespace Silean.Modules.AddSub

open Silean
open Silean.Authoring

/-! # Fixed-width addition and subtraction

The behavioral contract below uses direct carry/borrow recursion. The hardware
separately implements subtraction as `left + ~right + 1`. Structural
certification is in `Internal/AddSubVerification.lean`; the supported proof
boundary is `AddSubTheorems.lean`. -/

private def sumBit (left right carry : Bool) : Bool :=
  Primitives.xorValue (Primitives.xorValue left right) carry

private def carryBit (left right carry : Bool) : Bool :=
  (left && right) || (left && carry) || (right && carry)

private def borrowBit (left right borrow : Bool) : Bool :=
  (!left && (right || borrow)) || (right && borrow)

/-! In subtraction mode the internal chain is borrow and the returned flag is
its complement, so `carryOut = true` means that no borrow occurred. -/
private def operate : (width : Nat) → (Fin width → Bool) →
    (Fin width → Bool) → Bool → Bool → (Fin width → Bool) × Bool
  | 0, _, _, subtract, chain =>
      (fun index => Fin.elim0 index, if subtract then !chain else chain)
  | width + 1, left, right, subtract, chain =>
      let lower := operate width
        (fun index => left index.castSucc)
        (fun index => right index.castSucc) subtract chain
      let incoming := if subtract then !lower.2 else lower.2
      let high := sumBit (left (Fin.last width)) (right (Fin.last width)) incoming
      let outgoing := if subtract then
        borrowBit (left (Fin.last width)) (right (Fin.last width)) incoming
      else carryBit (left (Fin.last width)) (right (Fin.last width)) incoming
      (Fin.lastCases high lower.1, if subtract then !outgoing else outgoing)

/-- Natural add/subtract behavior, initialized with neither carry nor borrow. -/
def addSubBits (width : Nat) (left right : Fin width → Bool) (subtract : Bool) :
    (Fin width → Bool) × Bool :=
  operate width left right subtract false

private theorem addBits_transformed : ∀ (width : Nat)
    (left right : Fin width → Bool) (subtract chain : Bool),
    Add.addBits width left
        (fun index => Primitives.xorValue (right index) subtract)
        (if subtract then !chain else chain) =
      operate width left right subtract chain
  | 0, _, _, subtract, chain => by simp [Add.addBits, operate]
  | width + 1, left, right, subtract, chain => by
      have lower := addBits_transformed width
        (fun index => left index.castSucc)
        (fun index => right index.castSucc) subtract chain
      simp only [Add.addBits, operate]
      rw [lower]
      cases lowerOp : operate width (fun index => left index.castSucc)
          (fun index => right index.castSucc) subtract chain with
      | mk lowerBits lowerFlag =>
          cases subtract <;> cases lowerFlag <;>
            cases leftHigh : left (Fin.last width) <;>
            cases rightHigh : right (Fin.last width) <;>
            simp [Add.sumBit, Add.carryBit, sumBit, carryBit, borrowBit,
              Primitives.xorValue]

theorem addBits_xorRight_eq_addSubBits (width : Nat)
    (left right : Fin width → Bool) (subtract : Bool) :
    Add.addBits width left
        (fun index => Primitives.xorValue (right index) subtract) subtract =
      addSubBits width left right subtract := by
  simpa [addSubBits] using addBits_transformed width left right subtract false

private theorem complemented_toNat : ∀ (width : Nat) (value : Fin width → Bool),
    BitVector.toNat width (fun index => Primitives.xorValue (value index) true) +
        BitVector.toNat width value + 1 = BitVector.cardinality width
  | 0, _ => by simp [BitVector.toNat, BitVector.cardinality]
  | width + 1, value => by
      have lower := complemented_toNat width (fun index => value index.castSucc)
      cases high : value (Fin.last width) <;>
        simp [BitVector.toNat, BitVector.cardinality, high,
          Primitives.xorValue] at lower ⊢ <;>
        omega

/-- The result is ordinary addition or modular subtraction, independent of
the two's-complement implementation used by the structure. -/
theorem addSubBits_result_toNat (width : Nat) (left right : Fin width → Bool)
    (subtract : Bool) :
    BitVector.toNat width (addSubBits width left right subtract).1 =
      if subtract then
        (BitVector.toNat width left + BitVector.cardinality width -
          BitVector.toNat width right) % BitVector.cardinality width
      else
        (BitVector.toNat width left + BitVector.toNat width right) %
          BitVector.cardinality width := by
  have equation := Add.addBits_numeric width left
    (fun index => Primitives.xorValue (right index) subtract) subtract
  rw [addBits_xorRight_eq_addSubBits] at equation
  have resultBound := BitVector.toNat_lt_cardinality width
    (addSubBits width left right subtract).1
  have resultBoundPow : BitVector.toNat width (addSubBits width left right subtract).1 <
      2 ^ width := by simpa using resultBound
  cases subtract with
  | false =>
      simp [Primitives.xorValue] at equation ⊢
      rw [← equation]
      simp [Nat.add_mod, Nat.mod_eq_of_lt resultBoundPow]
  | true =>
      have complement := complemented_toNat width right
      have rightBound := BitVector.toNat_lt_cardinality width right
      simp at equation ⊢
      rw [BitVector.cardinality_eq_pow] at complement rightBound
      have transformedSum :
          BitVector.toNat width left +
              BitVector.toNat width
                (fun index => Primitives.xorValue (right index) true) + 1 =
            BitVector.toNat width left + 2 ^ width -
              BitVector.toNat width right := by
        omega
      rw [← transformedSum, ← equation]
      simp [Nat.add_mod, Nat.mod_eq_of_lt resultBoundPow]

/-- In subtraction mode carry-out is the conventional no-borrow flag. -/
theorem addSubBits_carry_subtract (width : Nat) (left right : Fin width → Bool) :
    (addSubBits width left right true).2 =
      decide (BitVector.toNat width right ≤ BitVector.toNat width left) := by
  have equation := Add.addBits_numeric width left
    (fun index => Primitives.xorValue (right index) true) true
  rw [addBits_xorRight_eq_addSubBits] at equation
  have complement := complemented_toNat width right
  have leftBound := BitVector.toNat_lt_cardinality width left
  have rightBound := BitVector.toNat_lt_cardinality width right
  have resultBound := BitVector.toNat_lt_cardinality width
    (addSubBits width left right true).1
  rw [BitVector.cardinality_eq_pow] at complement leftBound rightBound resultBound
  cases carry : (addSubBits width left right true).2 <;>
    by_cases noBorrow : BitVector.toNat width right ≤ BitVector.toNat width left <;>
    simp [carry, noBorrow] at equation ⊢ <;>
    omega

def outputRule (width : Nat) :
    Contracts.Cycle.CycleOutputRule (ports width) emptySignalMap where
  readsInputs := .all (ports width).inputs
  writesOutputs := .all (ports width).outputs
  target inputs _ := fun
    | .result => (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).1
    | .carryOut => (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).2

module_cycle_contract cycleContract (width : Nat) for ports width where
  state := emptySignalMap
  output_rule apply := outputRule width
  state_rule := Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .result =
        (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).1 ∧
      outputs .carryOut =
        (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).2 := by
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

/-- The observable result and carry/no-borrow flag of the selected operation. -/
structure Behavior (width : Nat) (inputs : (ports width).inputs.Values)
    (outputs : (ports width).outputs.Values) : Prop where
  result : outputs .result =
    (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).1
  carryOut : outputs .carryOut =
    (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).2

namespace Behavior

/-- An allowed contract step has the add/subtract unit's complete behavior. -/
theorem of_allowed (width : Nat) {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step) :
    Behavior width step.inputs step.outputs := by
  rcases (outputRule_holds_iff width step.inputs step.currentState
    step.outputs).mp (allowed.1 .apply) with ⟨result, carryOut⟩
  exact ⟨result, carryOut⟩

/-- The result is addition or modular subtraction according to `subtract`. -/
theorem result_toNat {width : Nat} {inputs : (ports width).inputs.Values}
    {outputs : (ports width).outputs.Values}
    (behavior : Behavior width inputs outputs) :
    BitVector.toNat width (outputs .result) =
      bif inputs .subtract then
        (BitVector.toNat width (inputs .left) + BitVector.cardinality width -
          BitVector.toNat width (inputs .right)) % BitVector.cardinality width
      else
        (BitVector.toNat width (inputs .left) +
          BitVector.toNat width (inputs .right)) %
            BitVector.cardinality width := by
  rw [behavior.result]
  have result := addSubBits_result_toNat width
    (inputs .left) (inputs .right) (inputs .subtract)
  cases subtract : inputs .subtract <;>
    simp [subtract] at result ⊢ <;> exact result

/-- In subtraction mode, carry-out is true exactly when no borrow occurred. -/
theorem carry_eq_noBorrow {width : Nat}
    {inputs : (ports width).inputs.Values}
    {outputs : (ports width).outputs.Values}
    (behavior : Behavior width inputs outputs)
    (subtracts : inputs .subtract = true) :
    outputs .carryOut =
      decide (BitVector.toNat width (inputs .right) ≤
        BitVector.toNat width (inputs .left)) := by
  rw [behavior.carryOut, subtracts]
  exact addSubBits_carry_subtract width (inputs .left) (inputs .right)

end Behavior

/-! ## Authored hardware -/

namespace Description

open Authoring.CircuitDescription
open Authoring.CircuitLogic
open scoped Authoring.CircuitLogic

noncomputable def construction (width : Nat) : Builder Unit := do
  let left ← input "left" (.vector width .bit)
  let right ← input "right" (.vector width .bit)
  let subtract ← input "subtract" .bit
  wire transformedRight ← right ^^^ (←
    combine (subtractVector width) fun _ => subtract)
  let added ← Add.place left transformedRight subtract
  output "result" added.result
  output "carryOut" added.carryOut

noncomputable def description (width : Nat) : Description :=
  build (construction width)

end Description

/-! ## Placement -/

open Authoring.CircuitDescription

/-- Outputs produced by a placed add/subtract unit. -/
structure PlacedOutputs (width : Nat) where
  result : Net (.vector width .bit)
  carryOut : Net .bit

/-- Place an add/subtract unit under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (left right : Net (.vector width .bit)) (subtract : Net .bit) :
    Builder (PlacedOutputs width) := do
  let child ← Authoring.CircuitDescription.placeNamed name (design width) fun
    | .left => left
    | .right => right
    | .subtract => subtract
  pure { result := child .result, carryOut := child .carryOut }

/-- Place an add/subtract unit using the next conventional indexed name. -/
noncomputable def place
    (left right : Net (.vector width .bit)) (subtract : Net .bit) :
    Builder (PlacedOutputs width) := do
  let child ← placeIndexed "add_sub" (design width) fun
    | .left => left
    | .right => right
    | .subtract => subtract
  pure { result := child .result, carryOut := child .carryOut }

attribute [circuit_description] placeNamed place

end Silean.Modules.AddSub
