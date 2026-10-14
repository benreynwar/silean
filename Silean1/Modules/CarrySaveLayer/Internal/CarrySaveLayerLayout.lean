import Silean.Modules.CarrySaveLayer.CarrySaveLayer
import Silean.Modules.VectorReindex.VectorReindex

/-! Typed index layout shared by the layer structure and its arithmetic model. -/

namespace Silean.Modules.CarrySaveLayer.Internal

open Silean

theorem groupCount_add_three (operandCount : Nat) :
    groupCount (operandCount + 3) = groupCount operandCount + 1 := by
  unfold groupCount
  omega

theorem remainderCount_add_three (operandCount : Nat) :
    remainderCount (operandCount + 3) = remainderCount operandCount := by
  unfold remainderCount
  omega

theorem reducedCount_add_three (operandCount : Nat) :
    reducedCount (operandCount + 3) = reducedCount operandCount + 2 := by
  unfold reducedCount groupCount remainderCount
  omega

/-- Select one of the three operands belonging to a complete group. -/
def groupedInputIndex (operandCount : Nat)
    (group : Fin (groupCount operandCount)) (offset : Fin 3) :
    Fin operandCount :=
  ⟨3 * group.val + offset.val, by
    have groupBound : group.val < operandCount / 3 := group.isLt
    have offsetBound : offset.val < 3 := offset.isLt
    have divided := Nat.div_mul_le_self operandCount 3
    omega⟩

/-- Select an operand left after all complete triples. -/
def remainderInputIndex (operandCount : Nat)
    (index : Fin (remainderCount operandCount)) : Fin operandCount :=
  ⟨3 * groupCount operandCount + index.val, by
    have indexBound : index.val < operandCount % 3 := index.isLt
    have division := Nat.mod_add_div operandCount 3
    unfold groupCount remainderCount
    omega⟩

def firstGroup (operandCount : Nat) :
    Fin (groupCount (operandCount + 3)) :=
  Fin.cast (groupCount_add_three operandCount).symm 0

def laterGroup (operandCount : Nat)
    (group : Fin (groupCount operandCount)) :
    Fin (groupCount (operandCount + 3)) :=
  Fin.cast (groupCount_add_three operandCount).symm group.succ

@[simp] theorem groupedInputIndex_firstGroup (operandCount : Nat)
    (offset : Fin 3) :
    groupedInputIndex (operandCount + 3) (firstGroup operandCount) offset =
      ⟨offset.val, by omega⟩ := by
  apply Fin.ext
  simp [groupedInputIndex, firstGroup, Fin.cast]

@[simp] theorem groupedInputIndex_laterGroup (operandCount : Nat)
    (group : Fin (groupCount operandCount)) (offset : Fin 3) :
    groupedInputIndex (operandCount + 3) (laterGroup operandCount group) offset =
      ⟨(groupedInputIndex operandCount group offset).val + 3, by
        have bound := (groupedInputIndex operandCount group offset).isLt
        omega⟩ := by
  apply Fin.ext
  simp [groupedInputIndex, laterGroup, Fin.cast]
  omega

@[simp] theorem remainderInputIndex_add_three (operandCount : Nat)
    (index : Fin (remainderCount operandCount)) :
    remainderInputIndex (operandCount + 3)
        (Fin.cast (remainderCount_add_three operandCount).symm index) =
      ⟨(remainderInputIndex operandCount index).val + 3, by
        have bound := (remainderInputIndex operandCount index).isLt
        omega⟩ := by
  apply Fin.ext
  simp [remainderInputIndex, groupCount, Fin.cast]
  omega

/-- Interleave each group's sum and carry, then append the ungrouped operands.
The definition is generic so structural signal sources and pure values use the
same typed layout. -/
def interleave {α : Sort _} :
    (operandCount : Nat) →
      (Fin (groupCount operandCount) → α) →
      (Fin (groupCount operandCount) → α) →
      (Fin (remainderCount operandCount) → α) →
      Fin (reducedCount operandCount) → α
  | 0, _, _, remainder => remainder
  | 1, _, _, remainder => remainder
  | 2, _, _, remainder => remainder
  | operandCount + 3, sums, carries, remainder => fun index =>
      let shifted : Fin (reducedCount operandCount + 2) :=
        Fin.cast (reducedCount_add_three operandCount) index
      Fin.cases
        (sums (firstGroup operandCount))
        (fun afterSum => Fin.cases
          (carries (firstGroup operandCount))
          (interleave operandCount
            (fun group => sums (laterGroup operandCount group))
            (fun group => carries (laterGroup operandCount group))
            (fun index => remainder
              (Fin.cast (remainderCount_add_three operandCount).symm index)))
          afterSum)
        shifted
termination_by operandCount => operandCount

/-- Place sums first, then carries, then operands which bypass compression. -/
def flatten {α : Sort _} (operandCount : Nat)
    (sums carries : Fin (groupCount operandCount) → α)
    (remainder : Fin (remainderCount operandCount) → α) :
    Fin (reducedCount operandCount) → α :=
  Fin.addCases sums (Fin.addCases carries remainder)

def sumFlatIndex (operandCount : Nat)
    (group : Fin (groupCount operandCount)) :
    Fin (reducedCount operandCount) :=
  Fin.castAdd (groupCount operandCount + remainderCount operandCount) group

def carryFlatIndex (operandCount : Nat)
    (group : Fin (groupCount operandCount)) :
    Fin (reducedCount operandCount) :=
  Fin.natAdd (groupCount operandCount)
    (Fin.castAdd (remainderCount operandCount) group)

def remainderFlatIndex (operandCount : Nat)
    (index : Fin (remainderCount operandCount)) :
    Fin (reducedCount operandCount) :=
  Fin.natAdd (groupCount operandCount)
    (Fin.natAdd (groupCount operandCount) index)

@[simp] theorem flatten_sum (operandCount : Nat)
    (sums carries : Fin (groupCount operandCount) → α)
    (remainder : Fin (remainderCount operandCount) → α)
    (group : Fin (groupCount operandCount)) :
    flatten operandCount sums carries remainder (sumFlatIndex operandCount group) =
      sums group := by
  simp [flatten, sumFlatIndex]

@[simp] theorem flatten_carry (operandCount : Nat)
    (sums carries : Fin (groupCount operandCount) → α)
    (remainder : Fin (remainderCount operandCount) → α)
    (group : Fin (groupCount operandCount)) :
    flatten operandCount sums carries remainder
        (carryFlatIndex operandCount group) = carries group := by
  simp [flatten, carryFlatIndex]

@[simp] theorem flatten_remainder (operandCount : Nat)
    (sums carries : Fin (groupCount operandCount) → α)
    (remainder : Fin (remainderCount operandCount) → α)
    (index : Fin (remainderCount operandCount)) :
    flatten operandCount sums carries remainder
        (remainderFlatIndex operandCount index) = remainder index := by
  simp [flatten, remainderFlatIndex]

/-- Mapping every entry commutes with the flat intermediate layout. -/
theorem map_flatten {α : Sort _} {β : Sort _} (map : α → β)
    (operandCount : Nat)
    (sums carries : Fin (groupCount operandCount) → α)
    (remainder : Fin (remainderCount operandCount) → α)
    (index : Fin (reducedCount operandCount)) :
    map (flatten operandCount sums carries remainder index) =
      flatten operandCount (fun group => map (sums group))
        (fun group => map (carries group))
        (fun rest => map (remainder rest)) index := by
  refine Fin.addCases ?_ ?_ index
  · intro group
    simp [flatten]
  · intro rest
    refine Fin.addCases ?_ ?_ rest
    · intro group
      simp [flatten]
    · intro remainderIndex
      simp [flatten]

/-- The static permutation from the flat intermediate vector to the desired
sum/carry interleaving. -/
def interleaveLayout (operandCount : Nat) :
    Fin (reducedCount operandCount) → Fin (reducedCount operandCount) :=
  interleave operandCount
    (sumFlatIndex operandCount)
    (carryFlatIndex operandCount)
    (remainderFlatIndex operandCount)

private theorem map_fin_cases {α : Sort _} {β : Sort _} (map : α → β)
    (head : α) (tail : Fin count → α) (index : Fin (count + 1)) :
    map (Fin.cases head tail index) =
      Fin.cases (map head) (fun rest => map (tail rest)) index := by
  exact Fin.cases rfl (fun _ => rfl) index

/-- Mapping every entry commutes with the typed interleaving layout. -/
theorem map_interleave {α : Sort _} {β : Sort _} (map : α → β) :
    ∀ (operandCount : Nat)
      (sums carries : Fin (groupCount operandCount) → α)
      (remainder : Fin (remainderCount operandCount) → α)
      (index : Fin (reducedCount operandCount)),
      map (interleave operandCount sums carries remainder index) =
        interleave operandCount (fun group => map (sums group))
          (fun group => map (carries group))
          (fun rest => map (remainder rest)) index
  | 0, _, _, _, _ => by simp [interleave]
  | 1, _, _, _, _ => by simp [interleave]
  | 2, _, _, _, _ => by simp [interleave]
  | operandCount + 3, sums, carries, remainder, index => by
      simp only [interleave]
      rw [map_fin_cases map]
      refine Fin.cases ?_ (fun afterSum => ?_)
        (Fin.cast (reducedCount_add_three operandCount) index)
      · rfl
      · simp only [Fin.cases_succ]
        rw [map_fin_cases map]
        refine Fin.cases ?_ (fun restIndex => ?_) afterSum
        · rfl
        · exact map_interleave map operandCount
            (fun group => sums (laterGroup operandCount group))
            (fun group => carries (laterGroup operandCount group))
            (fun rest => remainder
              (Fin.cast (remainderCount_add_three operandCount).symm rest))
            restIndex

/-- Reindexing the flat intermediate vector produces the natural interleaved
collection. -/
theorem reindex_flatten (operandCount : Nat)
    (sums carries : Fin (groupCount operandCount) → α)
    (remainder : Fin (remainderCount operandCount) → α) :
    VectorReindex.apply (interleaveLayout operandCount)
        (flatten operandCount sums carries remainder) =
      interleave operandCount sums carries remainder := by
  funext index
  simp only [VectorReindex.apply, interleaveLayout]
  rw [map_interleave
    (flatten operandCount sums carries remainder)
    operandCount
    (sumFlatIndex operandCount)
    (carryFlatIndex operandCount)
    (remainderFlatIndex operandCount)
    index]
  simp

end Silean.Modules.CarrySaveLayer.Internal
