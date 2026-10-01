import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector

/-! # Vector concatenation

`VectorConcat` joins two vectors of the same element type, placing the left
vector at the lower result indices.
-/

namespace Silean.Modules.VectorConcat

open Silean
open Silean.Authoring

module_ports ports (element : SignalType) (leftWidth : Nat) (rightWidth : Nat)
    with (elementNaming : Naming.SignalTypeNaming element :=
      .positional element) where
  input left (schema := .vector elementNaming) : .vector leftWidth element,
  input right (schema := .vector elementNaming) : .vector rightWidth element,
  output result (schema := .vector elementNaming) :
    .vector (leftWidth + rightWidth) element

def concat (left : Fin leftWidth → α) (right : Fin rightWidth → α) :
    Fin (leftWidth + rightWidth) → α :=
  Fin.addCases left right

@[simp] theorem concat_left (left : Fin leftWidth → α)
    (right : Fin rightWidth → α) (index : Fin leftWidth) :
    concat left right (Fin.castAdd rightWidth index) = left index := by
  simp [concat]

@[simp] theorem concat_right (left : Fin leftWidth → α)
    (right : Fin rightWidth → α) (index : Fin rightWidth) :
    concat left right (Fin.natAdd leftWidth index) = right index := by
  simp [concat]

/-- Unsigned interpretation of a concatenation: the left vector supplies
the low bits and the right vector supplies the high bits. -/
theorem toNat_concat (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    BitVector.toNat (leftWidth + rightWidth) (concat left right) =
      BitVector.toNat leftWidth left +
        BitVector.cardinality leftWidth * BitVector.toNat rightWidth right := by
  induction rightWidth with
  | zero =>
      have equal : concat left right = left := by
        funext index
        change Fin.addCases left right (Fin.castAdd 0 index) = left index
        exact Fin.addCases_left index
      rw [equal]
      simp [BitVector.toNat]
  | succ rightWidth induction =>
      simp only [Nat.add_succ, BitVector.toNat]
      have highEqual :
          concat left right (Fin.last (leftWidth + rightWidth)) =
            right (Fin.last rightWidth) := by
        rw [show Fin.last (leftWidth + rightWidth) =
            Fin.natAdd leftWidth (Fin.last rightWidth) by
          apply Fin.ext
          simp]
        exact concat_right left right (Fin.last rightWidth)
      have lowerEqual :
          (fun index : Fin (leftWidth + rightWidth) =>
            concat left right index.castSucc) =
          concat left (fun index => right index.castSucc) := by
        funext index
        refine Fin.addCases (motive := fun index =>
          concat left right index.castSucc =
            concat left (fun index => right index.castSucc) index) ?_ ?_ index
        · intro low
          rw [show (Fin.castAdd rightWidth low).castSucc =
              Fin.castAdd (rightWidth + 1) low by
            apply Fin.ext
            rfl]
          simp [concat]
        · intro high
          rw [show (Fin.natAdd leftWidth high).castSucc =
              Fin.natAdd leftWidth high.castSucc by
            apply Fin.ext
            rfl]
          simp [concat]
      change
        ((if concat left right (Fin.last (leftWidth + rightWidth)) then
            BitVector.cardinality (leftWidth + rightWidth) else 0) +
          BitVector.toNat (leftWidth + rightWidth)
            (fun index => concat left right index.castSucc)) =
          BitVector.toNat leftWidth left +
            BitVector.cardinality leftWidth *
              ((if right (Fin.last rightWidth) then
                  BitVector.cardinality rightWidth else 0) +
                BitVector.toNat rightWidth
                  (fun index => right index.castSucc))
      cases high : right (Fin.last rightWidth) with
      | false =>
          have concatHigh :
              concat left right (Fin.last (leftWidth + rightWidth)) = false :=
            highEqual.trans high
          rw [concatHigh]
          simp only [Bool.false_eq_true, if_false, Nat.zero_add]
          rw [lowerEqual, induction (fun index => right index.castSucc)]
      | true =>
          have concatHigh :
              concat left right (Fin.last (leftWidth + rightWidth)) = true :=
            highEqual.trans high
          rw [concatHigh]
          simp only [if_true]
          rw [lowerEqual, induction (fun index => right index.castSucc)]
          simp only [BitVector.cardinality_eq_pow, Nat.pow_add]
          rw [Nat.mul_add]
          omega

module_cycle_contract cycleContract (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat)
    for ports element leftWidth rightWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [left, right]
    writes := { result := concat left right }
  state_rule where
    reads := []
    next := {}

theorem result_left_of_allowed (element : SignalType) (leftWidth rightWidth : Nat)
    {step : (cycleContract element leftWidth rightWidth).Step}
    (allowed : (cycleContract element leftWidth rightWidth).Allows step)
    (index : Fin leftWidth) :
    step.outputs .result (Fin.castAdd rightWidth index) =
      step.inputs .left index := by
  rw [cycleContract.result element leftWidth rightWidth allowed]
  exact concat_left _ _ index

theorem result_right_of_allowed (element : SignalType) (leftWidth rightWidth : Nat)
    {step : (cycleContract element leftWidth rightWidth).Step}
    (allowed : (cycleContract element leftWidth rightWidth).Allows step)
    (index : Fin rightWidth) :
    step.outputs .result (Fin.natAdd leftWidth index) =
      step.inputs .right index := by
  rw [cycleContract.result element leftWidth rightWidth allowed]
  exact concat_right _ _ index

end Silean.Modules.VectorConcat
