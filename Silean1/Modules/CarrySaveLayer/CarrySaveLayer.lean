import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector

/-! # Carry-save compression layer

`CarrySaveLayer` performs one parallel three-to-two compression step over a
statically sized collection of equal-width operands. Its public contract says
only that the shorter collection preserves the total modulo the vector width;
the grouping and placement of individual compressors are implementation
details.
-/

namespace Silean.Modules.CarrySaveLayer

open Silean

/-- Number of complete triples compressed by one layer. -/
def groupCount (operandCount : Nat) : Nat := operandCount / 3

/-- Number of operands not belonging to a complete triple. -/
def remainderCount (operandCount : Nat) : Nat := operandCount % 3

/-- Number of operands produced by one parallel compression layer. -/
def reducedCount (operandCount : Nat) : Nat :=
  groupCount operandCount + (groupCount operandCount + remainderCount operandCount)

theorem reducedCount_lt (operandCount : Nat) (atLeastThree : 3 ≤ operandCount) :
    reducedCount operandCount < operandCount := by
  unfold reducedCount groupCount remainderCount
  omega

module_ports ports (width : Nat) (operandCount : Nat) where
  input operands : .vector operandCount (.vector width .bit),
  output reduced : .vector (reducedCount operandCount) (.vector width .bit)

/-- The ordinary natural-number total of a fixed-size operand collection. -/
def total (width operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool) : Nat :=
  (List.ofFn fun index => BitVector.toNat width (operands index)).sum

@[simp] theorem total_zero (width : Nat)
    (operands : Fin 0 → Fin width → Bool) :
    total width 0 operands = 0 := by
  simp [total]

theorem total_succ (width operandCount : Nat)
    (operands : Fin (operandCount + 1) → Fin width → Bool) :
    total width (operandCount + 1) operands =
      BitVector.toNat width (operands 0) +
        total width operandCount (fun index => operands index.succ) := by
  simp [total, List.ofFn_succ]

/-- One compression layer preserves the collection total at the fixed width. -/
def PreservesTotal (width operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool)
    (reduced : Fin (reducedCount operandCount) → Fin width → Bool) : Prop :=
  total width (reducedCount operandCount) reduced % BitVector.cardinality width =
    total width operandCount operands % BitVector.cardinality width

/-- A collection too small to compress passes through unchanged. -/
def NaturalBaseCase (width : Nat) :
    (operandCount : Nat) →
      (Fin operandCount → Fin width → Bool) →
      (Fin (reducedCount operandCount) → Fin width → Bool) → Prop
  | 0, operands, reduced => reduced = operands
  | 1, operands, reduced => reduced = operands
  | 2, operands, reduced => reduced = operands
  | _ + 3, _, _ => True

/-- The public relational contract of one carry-save compression layer. -/
def Accepts (width operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool)
    (reduced : Fin (reducedCount operandCount) → Fin width → Bool) : Prop :=
  PreservesTotal width operandCount operands reduced ∧
    NaturalBaseCase width operandCount operands reduced

/-- The custom contract applied to values at the module boundary. -/
def contract (width operandCount : Nat) :
    (ports width operandCount).inputs.Values →
      (ports width operandCount).outputs.Values → Prop :=
  fun inputs outputs =>
    Accepts width operandCount (inputs .operands) (outputs .reduced)

/-- The arithmetic fact consumed by a recursive tree or another parent. -/
theorem preservesTotal_of_contract (width operandCount : Nat)
    {inputs : (ports width operandCount).inputs.Values}
    {outputs : (ports width operandCount).outputs.Values}
    (accepted : contract width operandCount inputs outputs) :
    PreservesTotal width operandCount (inputs .operands) (outputs .reduced) :=
  accepted.1

@[simp] theorem accepts_zero_iff (width : Nat)
    (operands : Fin 0 → Fin width → Bool)
    (reduced : Fin (reducedCount 0) → Fin width → Bool) :
    Accepts width 0 operands reduced ↔ reduced = operands := by
  simp [Accepts, PreservesTotal, NaturalBaseCase, total, reducedCount,
    groupCount, remainderCount]

@[simp] theorem accepts_one_iff (width : Nat)
    (operands : Fin 1 → Fin width → Bool)
    (reduced : Fin (reducedCount 1) → Fin width → Bool) :
    Accepts width 1 operands reduced ↔ reduced = operands := by
  constructor
  · exact fun accepted => accepted.2
  · rintro rfl
    exact ⟨rfl, rfl⟩

@[simp] theorem accepts_two_iff (width : Nat)
    (operands : Fin 2 → Fin width → Bool)
    (reduced : Fin (reducedCount 2) → Fin width → Bool) :
    Accepts width 2 operands reduced ↔ reduced = operands := by
  constructor
  · exact fun accepted => accepted.2
  · rintro rfl
    exact ⟨rfl, rfl⟩

end Silean.Modules.CarrySaveLayer
