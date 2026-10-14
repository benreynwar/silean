import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector

/-! # Carry-save tree

`CarrySaveTree` reduces a statically sized collection of equal-width operands
to two operands. This file specifies only the observable arithmetic relation;
the choice of compressor grouping and hardware hierarchy is deliberately not
part of the public contract.

Unlike `ModuleCycleContract`, this contract is relational: for collections of
three or more operands, several output pairs may represent the same preserved
total. The structural correctness theorem will establish this relation
directly rather than introducing a second, deterministic behavioral contract.
-/

namespace Silean.Modules.CarrySaveTree

open Silean

module_ports ports (width : Nat) (operandCount : Nat) where
  input operands : .vector operandCount (.vector width .bit),
  output resultA : .vector width .bit,
  output resultB : .vector width .bit

/-- The ordinary natural-number sum of all input operands. -/
def inputTotal (width operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool) : Nat :=
  (List.ofFn fun index => BitVector.toNat width (operands index)).sum

/-- The ordinary natural-number sum represented by the two outputs. -/
def outputTotal (width : Nat)
    (resultA resultB : Fin width → Bool) : Nat :=
  BitVector.toNat width resultA + BitVector.toNat width resultB

/-- The two outputs preserve the input total at the fixed vector width. -/
def PreservesTotal (width operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool)
    (resultA resultB : Fin width → Bool) : Prop :=
  outputTotal width resultA resultB % BitVector.cardinality width =
    inputTotal width operandCount operands % BitVector.cardinality width

/-- Collections already containing at most two operands pass through without
inventing a representation choice. Larger collections have no canonical
output pair at this abstraction boundary. -/
def NaturalBaseCase (width : Nat) :
    (operandCount : Nat) →
      (Fin operandCount → Fin width → Bool) →
      (Fin width → Bool) → (Fin width → Bool) → Prop
  | 0, _, resultA, resultB =>
      resultA = BitVector.ofNat width 0 ∧
        resultB = BitVector.ofNat width 0
  | 1, operands, resultA, resultB =>
      resultA = operands 0 ∧ resultB = BitVector.ofNat width 0
  | 2, operands, resultA, resultB =>
      resultA = operands 0 ∧ resultB = operands 1
  | _ + 3, _, _, _ => True

/-- The public relational contract of the carry-save tree. -/
def Accepts (width operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool)
    (resultA resultB : Fin width → Bool) : Prop :=
  PreservesTotal width operandCount operands resultA resultB ∧
    NaturalBaseCase width operandCount operands resultA resultB

/-- The public contract applied directly to values at the declared boundary. -/
def contract (width operandCount : Nat) :
    (ports width operandCount).inputs.Values →
      (ports width operandCount).outputs.Values → Prop :=
  fun inputs outputs =>
    Accepts width operandCount (inputs .operands)
      (outputs .resultA) (outputs .resultB)

theorem preservesTotal_of_accepts (width operandCount : Nat)
    {operands : Fin operandCount → Fin width → Bool}
    {resultA resultB : Fin width → Bool}
    (accepted : Accepts width operandCount operands resultA resultB) :
    PreservesTotal width operandCount operands resultA resultB :=
  accepted.1

/-- The arithmetic fact a parent module obtains from the boundary contract. -/
theorem preservesTotal_of_contract (width operandCount : Nat)
    {inputs : (ports width operandCount).inputs.Values}
    {outputs : (ports width operandCount).outputs.Values}
    (accepted : contract width operandCount inputs outputs) :
    PreservesTotal width operandCount (inputs .operands)
      (outputs .resultA) (outputs .resultB) :=
  accepted.1

@[simp] theorem accepts_zero_iff (width : Nat)
    (operands : Fin 0 → Fin width → Bool)
    (resultA resultB : Fin width → Bool) :
    Accepts width 0 operands resultA resultB ↔
      resultA = BitVector.ofNat width 0 ∧
        resultB = BitVector.ofNat width 0 := by
  constructor
  · exact fun accepted => accepted.2
  · rintro ⟨rfl, rfl⟩
    constructor
    · simp [PreservesTotal, inputTotal, outputTotal]
    · exact ⟨rfl, rfl⟩

@[simp] theorem accepts_one_iff (width : Nat)
    (operands : Fin 1 → Fin width → Bool)
    (resultA resultB : Fin width → Bool) :
    Accepts width 1 operands resultA resultB ↔
      resultA = operands 0 ∧ resultB = BitVector.ofNat width 0 := by
  constructor
  · exact fun accepted => accepted.2
  · rintro ⟨rfl, rfl⟩
    constructor
    · simp [PreservesTotal, inputTotal, outputTotal]
    · exact ⟨rfl, rfl⟩

@[simp] theorem accepts_two_iff (width : Nat)
    (operands : Fin 2 → Fin width → Bool)
    (resultA resultB : Fin width → Bool) :
    Accepts width 2 operands resultA resultB ↔
      resultA = operands 0 ∧ resultB = operands 1 := by
  constructor
  · exact fun accepted => accepted.2
  · rintro ⟨rfl, rfl⟩
    constructor
    · simp [PreservesTotal, inputTotal, outputTotal]
    · exact ⟨rfl, rfl⟩

end Silean.Modules.CarrySaveTree
