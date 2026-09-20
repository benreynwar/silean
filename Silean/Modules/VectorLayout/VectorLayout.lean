import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector

/-! # Vector layout

`VectorLayout` constructs a bit vector by selecting input bits or inserting
Boolean constants. It covers permutation, duplication, truncation, extension,
and constant insertion.
-/

namespace Silean.Modules.VectorLayout

open Silean
open Silean.Authoring

/-- The source selected for one output bit. -/
inductive BitSource (inputWidth : Nat) where
  | input (index : Fin inputWidth)
  | constant (value : Bool)
deriving DecidableEq, Repr

def BitSource.IsInput : BitSource inputWidth → Prop
  | .input _ => True
  | .constant _ => False

instance (source : BitSource inputWidth) : Decidable source.IsInput :=
  match source with
  | .input _ => isTrue trivial
  | .constant _ => isFalse id

def BitSource.inputIndex (source : BitSource inputWidth)
    (_ : source.IsInput) : Fin inputWidth :=
  match source with
  | .input index => index

def apply (layout : Fin outputWidth → BitSource inputWidth)
    (input : Fin inputWidth → Bool) : Fin outputWidth → Bool :=
  fun index => match layout index with
    | .input source => input source
    | .constant value => value

/-- Zero-extend a vector by `growthWidth` bits and statically shift it left.
The shift may range from zero through the complete growth width. -/
def wideningLeftShiftLayout (inputWidth growthWidth : Nat)
    (shift : Fin (growthWidth + 1)) :
    Fin (inputWidth + growthWidth) → BitSource inputWidth :=
  fun index =>
    if inRange : shift.val ≤ index.val ∧
        index.val < shift.val + inputWidth then
      .input ⟨index.val - shift.val, by omega⟩
    else
      .constant false

@[simp] theorem apply_wideningLeftShiftLayout (inputWidth growthWidth : Nat)
    (shift : Fin (growthWidth + 1)) (input : Fin inputWidth → Bool)
    (index : Fin (inputWidth + growthWidth)) :
    apply (wideningLeftShiftLayout inputWidth growthWidth shift) input index =
      if inRange : shift.val ≤ index.val ∧
          index.val < shift.val + inputWidth then
        input ⟨index.val - shift.val, by omega⟩
      else
        false := by
  by_cases inRange : shift.val ≤ index.val ∧
      index.val < shift.val + inputWidth
  · simp [apply, wideningLeftShiftLayout, inRange]
  · simp [apply, wideningLeftShiftLayout, inRange]

/-- A widening left-shift layout is the fixed-width encoding of a natural-number
left shift. The widened result has enough room for the complete shifted input. -/
theorem apply_wideningLeftShiftLayout_eq_ofNat
    (inputWidth growthWidth : Nat) (shift : Fin (growthWidth + 1))
    (input : Fin inputWidth → Bool) :
    apply (wideningLeftShiftLayout inputWidth growthWidth shift) input =
      BitVector.ofNat (inputWidth + growthWidth)
        (BitVector.toNat inputWidth input <<< shift.val) := by
  funext index
  rw [apply_wideningLeftShiftLayout]
  simp only [BitVector.ofNat, Nat.testBit_shiftLeft]
  by_cases lower : shift.val ≤ index.val
  · by_cases upper : index.val < shift.val + inputWidth
    · simp only [lower, upper, and_self, decide_true, dite_true]
      simpa using (BitVector.testBit_toNat inputWidth input
        ⟨index.val - shift.val, by omega⟩).symm
    · simp only [lower, upper, and_false, decide_true, dite_false]
      simpa using (BitVector.testBit_toNat_of_width_le inputWidth input
        (index.val - shift.val) (by omega)).symm
  · simp [lower]

module_ports ports (inputWidth : Nat) (outputWidth : Nat) where
  input input : .vector inputWidth .bit,
  output output : .vector outputWidth .bit

module_cycle_contract cycleContract (inputWidth : Nat) (outputWidth : Nat)
    (layout : Fin outputWidth → BitSource inputWidth)
    for ports inputWidth outputWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [input]
    writes := { output := VectorLayout.apply layout input }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.VectorLayout
