import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Foundation.BitVector
import Silean.Modules.Add
import Silean.Modules.BitwiseXor
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.AddSub

open Silean
open Silean.Authoring

/-! Fixed-width addition and subtraction. The behavioral contract below uses
direct carry/borrow recursion. The hardware separately implements subtraction
as `left + ~right + 1`. -/

module_ports ports (width : Nat) where
  input left : .vector width .bit,
  input right : .vector width .bit,
  input subtract : .bit,
  output result : .vector width .bit,
  output carryOut : .bit

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

/-! ## Hardware structure -/

def subtractVector (width : Nat) : Composition.SignalCombiner :=
  .vector width .bit

end Silean.Modules.AddSub

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design AddSub (width : Nat) where
  boundary (AddSub.ports width) (naming := AddSub.Naming.ports width)
  instances {
    -- Broadcasts `subtract` to every bit position.
    broadcastSubtract := Silean.Naming.SignalAdapter.combinerDesign
      (subtractVector width),
    -- Complements the right operand exactly in subtraction mode.
    transformRight := BitwiseXor.design (.vector width .bit),
    -- Adds the transformed operand and the subtraction carry-in.
    add := Add.design width }
  wiring {
    outputs {
      .result := add.result,
      .carryOut := add.carryOut }
    instance (.broadcastSubtract) {
      _ := input.subtract }
    instance (.transformRight) {
      .left := input.right,
      .right := broadcastSubtract.value }
    instance (.add) {
      .left := input.left,
      .right := transformRight.result,
      .carryIn := input.subtract }
  }

end Silean.Modules

namespace Silean.Modules.AddSub

open Silean
open Silean.Authoring

theorem result_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    outputs .result =
      (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).1 :=
  ((outputRule_holds_iff width inputs state outputs).mp (evaluates.1 .apply)).1

theorem carry_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    outputs .carryOut =
      (addSubBits width (inputs .left) (inputs .right) (inputs .subtract)).2 :=
  ((outputRule_holds_iff width inputs state outputs).mp (evaluates.1 .apply)).2

/-- Public modular arithmetic law for either selected operation. -/
theorem result_toNat_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    BitVector.toNat width (outputs .result) =
      bif inputs .subtract then
        (BitVector.toNat width (inputs .left) + BitVector.cardinality width -
          BitVector.toNat width (inputs .right)) % BitVector.cardinality width
      else
        (BitVector.toNat width (inputs .left) + BitVector.toNat width (inputs .right)) %
          BitVector.cardinality width := by
  rw [result_of_evaluatesTo width inputs state outputs nextState evaluates]
  have result := addSubBits_result_toNat width
    (inputs .left) (inputs .right) (inputs .subtract)
  cases subtract : inputs .subtract <;> simp [subtract] at result ⊢ <;> exact result

/-- In subtraction mode, the public carry output is true exactly when no
borrow was required. -/
theorem carry_eq_noBorrow_of_evaluatesTo (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) (nextState : emptySignalMap.Values)
    (subtracts : inputs .subtract = true)
    (evaluates : (cycleContract width).EvaluatesTo inputs state outputs nextState) :
    outputs .carryOut =
      decide (BitVector.toNat width (inputs .right) ≤
        BitVector.toNat width (inputs .left)) := by
  rw [carry_of_evaluatesTo width inputs state outputs nextState evaluates, subtracts]
  exact addSubBits_carry_subtract width (inputs .left) (inputs .right)

end Silean.Modules.AddSub
