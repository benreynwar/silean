import Silean.Modules.CarrySaveAdder.Internal.CarrySaveAdderArithmetic
import Silean.Modules.CarrySaveLayer.CarrySaveLayer
import Silean.Modules.CarrySaveLayer.Internal.CarrySaveLayerLayout

/-! Arithmetic model and preservation proof for one compression layer. -/

namespace Silean.Modules.CarrySaveLayer.Internal

open Silean

private def tailOperands (operands : Fin (operandCount + 3) → Fin width → Bool) :
    Fin operandCount → Fin width → Bool :=
  fun index => operands ⟨index.val + 3, by omega⟩

private theorem total_tail (width operandCount : Nat)
    (operands : Fin (operandCount + 3) → Fin width → Bool) :
    total width (operandCount + 3) operands =
      BitVector.toNat width (operands 0) +
      BitVector.toNat width (operands 1) +
      BitVector.toNat width (operands 2) +
      total width operandCount (tailOperands operands) := by
  rw [total_succ, total_succ, total_succ]
  have tails : (fun index : Fin operandCount => operands index.succ.succ.succ) =
      tailOperands operands := by
    funext index
    congr
  rw [tails]
  change BitVector.toNat width (operands 0) +
      (BitVector.toNat width (operands 1) +
        (BitVector.toNat width (operands 2) +
          total width operandCount (tailOperands operands))) = _
  omega

private theorem total_cast (width : Nat) {leftCount rightCount : Nat}
    (equal : leftCount = rightCount)
    (operands : Fin leftCount → Fin width → Bool) :
    total width rightCount (fun index => operands (Fin.cast equal.symm index)) =
      total width leftCount operands := by
  subst rightCount
  rfl

/-- Every complete triple has been replaced by two values with the same
fixed-width total. -/
def GroupsPreserveTotal (width operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool)
    (sums carries : Fin (groupCount operandCount) → Fin width → Bool) : Prop :=
  ∀ group,
    (BitVector.toNat width (sums group) +
        BitVector.toNat width (carries group)) % BitVector.cardinality width =
      CarrySaveAdder.totalValue width
        (operands (groupedInputIndex operandCount group 0))
        (operands (groupedInputIndex operandCount group 1))
        (operands (groupedInputIndex operandCount group 2)) %
          BitVector.cardinality width

/-- Operands outside complete triples are copied into the reduced collection. -/
def RemainderMatches (width operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool)
    (remainder : Fin (remainderCount operandCount) → Fin width → Bool) : Prop :=
  ∀ index, remainder index = operands (remainderInputIndex operandCount index)

/-- Interleaving pairwise group results and untouched remainder values
preserves the whole collection total when every group preserves its total. -/
theorem interleave_preservesTotal (width : Nat) : ∀ (operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool)
    (sums carries : Fin (groupCount operandCount) → Fin width → Bool)
    (remainder : Fin (remainderCount operandCount) → Fin width → Bool),
    GroupsPreserveTotal width operandCount operands sums carries →
    RemainderMatches width operandCount operands remainder →
    PreservesTotal width operandCount operands
      (interleave operandCount sums carries remainder)
  | 0, operands, sums, carries, remainder, _, _ => by
      simp [PreservesTotal, total, reducedCount, groupCount, remainderCount]
  | 1, operands, sums, carries, remainder, _, remainderMatches => by
      have outputEqual : interleave 1 sums carries remainder = operands := by
        funext index
        simp only [interleave]
        rw [remainderMatches index]
        apply congrArg operands
        apply Fin.ext
        simp [remainderInputIndex, groupCount]
      unfold PreservesTotal
      simpa [reducedCount, groupCount, remainderCount] using
        congrArg (fun values => total width 1 values %
          BitVector.cardinality width) outputEqual
  | 2, operands, sums, carries, remainder, _, remainderMatches => by
      have outputEqual : interleave 2 sums carries remainder = operands := by
        funext index
        simp only [interleave]
        rw [remainderMatches index]
        apply congrArg operands
        apply Fin.ext
        simp [remainderInputIndex, groupCount]
      unfold PreservesTotal
      simpa [reducedCount, groupCount, remainderCount] using
        congrArg (fun values => total width 2 values %
          BitVector.cardinality width) outputEqual
  | operandCount + 3, operands, sums, carries, remainder,
      groupsPreserve, remainderMatches => by
      let tailSums := fun group : Fin (groupCount operandCount) =>
        sums (laterGroup operandCount group)
      let tailCarries := fun group : Fin (groupCount operandCount) =>
        carries (laterGroup operandCount group)
      let tailRemainder := fun index : Fin (remainderCount operandCount) =>
        remainder (Fin.cast (remainderCount_add_three operandCount).symm index)
      have tailGroups : GroupsPreserveTotal width operandCount
          (tailOperands operands) tailSums tailCarries := by
        intro group
        have equation := groupsPreserve (laterGroup operandCount group)
        simpa [tailSums, tailCarries, tailOperands] using equation
      have tailMatches : RemainderMatches width operandCount
          (tailOperands operands) tailRemainder := by
        intro index
        have equation := remainderMatches
          (Fin.cast (remainderCount_add_three operandCount).symm index)
        simpa [tailRemainder, tailOperands] using equation
      have rest := interleave_preservesTotal width operandCount
        (tailOperands operands) tailSums tailCarries tailRemainder
        tailGroups tailMatches
      have head := groupsPreserve (firstGroup operandCount)
      have firstIndex :
          groupedInputIndex (operandCount + 3) (firstGroup operandCount) 0 = 0 := by
        apply Fin.ext
        simp [groupedInputIndex, firstGroup, Fin.cast]
      have secondIndex :
          groupedInputIndex (operandCount + 3) (firstGroup operandCount) 1 = 1 := by
        apply Fin.ext
        simp [groupedInputIndex, firstGroup, Fin.cast]
      have thirdIndex :
          groupedInputIndex (operandCount + 3) (firstGroup operandCount) 2 = 2 := by
        apply Fin.ext
        simp [groupedInputIndex, firstGroup, Fin.cast]
      have head' :
          (BitVector.toNat width (sums (firstGroup operandCount)) +
              BitVector.toNat width (carries (firstGroup operandCount))) %
                BitVector.cardinality width =
            (BitVector.toNat width (operands 0) +
              BitVector.toNat width (operands 1) +
              BitVector.toNat width (operands 2)) %
                BitVector.cardinality width := by
        rw [firstIndex, secondIndex, thirdIndex] at head
        simpa [CarrySaveAdder.totalValue] using head
      have reducedTotal :
          total width (reducedCount (operandCount + 3))
              (interleave (operandCount + 3) sums carries remainder) =
            BitVector.toNat width (sums (firstGroup operandCount)) +
            BitVector.toNat width (carries (firstGroup operandCount)) +
            total width (reducedCount operandCount)
              (interleave operandCount tailSums tailCarries tailRemainder) := by
        rw [← total_cast width (reducedCount_add_three operandCount)
          (interleave (operandCount + 3) sums carries remainder)]
        rw [total_succ, total_succ]
        have first : interleave (operandCount + 3) sums carries remainder
              (Fin.cast (reducedCount_add_three operandCount).symm 0) =
            sums (firstGroup operandCount) := by
          simp [interleave, Fin.cast]
        have second : interleave (operandCount + 3) sums carries remainder
              (Fin.cast (reducedCount_add_three operandCount).symm
                (Fin.succ (0 : Fin (reducedCount operandCount + 1)))) =
            carries (firstGroup operandCount) := by
          simp [interleave, Fin.cast]
          congr
        have restValues :
            (fun index : Fin (reducedCount operandCount) =>
              interleave (operandCount + 3) sums carries remainder
                (Fin.cast (reducedCount_add_three operandCount).symm
                  index.succ.succ)) =
              interleave operandCount tailSums tailCarries tailRemainder := by
          funext index
          simp [interleave, Fin.cast, tailSums, tailCarries, tailRemainder]
        rw [first, second, restValues]
        omega
      unfold PreservesTotal at rest ⊢
      rw [reducedTotal, total_tail width operandCount operands]
      rw [Nat.add_mod
        (BitVector.toNat width (sums (firstGroup operandCount)) +
          BitVector.toNat width (carries (firstGroup operandCount)))
        (total width (reducedCount operandCount)
          (interleave operandCount tailSums tailCarries tailRemainder))]
      rw [Nat.add_mod
        (BitVector.toNat width (operands 0) +
          BitVector.toNat width (operands 1) +
          BitVector.toNat width (operands 2))
        (total width operandCount (tailOperands operands))]
      rw [head', rest]

/-- Without a complete triple, the structural layout is exactly the original
operand collection. -/
theorem interleave_naturalBaseCase (width : Nat) : ∀ (operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool)
    (sums carries : Fin (groupCount operandCount) → Fin width → Bool)
    (remainder : Fin (remainderCount operandCount) → Fin width → Bool),
    RemainderMatches width operandCount operands remainder →
    NaturalBaseCase width operandCount operands
      (interleave operandCount sums carries remainder)
  | 0, _, _, _, _, _ => by
      funext index
      exact Fin.elim0 index
  | 1, operands, sums, carries, remainder, remainderAgrees => by
      funext index
      simp only [interleave]
      rw [remainderAgrees index]
      apply congrArg operands
      apply Fin.ext
      simp [remainderInputIndex, groupCount]
  | 2, operands, sums, carries, remainder, remainderAgrees => by
      funext index
      simp only [interleave]
      rw [remainderAgrees index]
      apply congrArg operands
      apply Fin.ext
      simp [remainderInputIndex, groupCount]
  | _ + 3, _, _, _, _, _ => trivial

end Silean.Modules.CarrySaveLayer.Internal
