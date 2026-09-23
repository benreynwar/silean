import HTFFT.Exact.Radix2
import Mathlib.Tactic

namespace HTFFT.Exact

/-- The coordinates of one value in an iterative radix-two butterfly layer.

At stage `s`, each group is a contiguous block of `2^(s+1)` values.  `branch`
selects the first (`0`) or second (`1`) half of that block, and `offset`
selects the same position within the two halves.  Consequently the two values
with equal `group` and `offset` are exactly `2^s` positions apart. -/
structure LayerPosition (depth : Nat) (stage : Fin depth) where
  group : Fin (2 ^ (depth - stage.val - 1))
  branch : Fin 2
  offset : Fin (2 ^ stage.val)
  deriving DecidableEq, Repr

private theorem layerSize (depth : Nat) (stage : Fin depth) :
    2 ^ (depth - stage.val - 1) * (2 * 2 ^ stage.val) = 2 ^ depth := by
  have hdepth : depth - stage.val - 1 + (stage.val + 1) = depth := by
    omega
  calc
    2 ^ (depth - stage.val - 1) * (2 * 2 ^ stage.val) =
        2 ^ (depth - stage.val - 1) * 2 ^ (stage.val + 1) := by
      rw [show stage.val + 1 = stage.val.succ by omega, Nat.pow_succ]
      simp [Nat.mul_comm]
    _ = 2 ^ (depth - stage.val - 1 + (stage.val + 1)) := by
      exact (Nat.pow_add 2 _ _).symm
    _ = 2 ^ depth := by rw [hdepth]

/-- The groups at one stage partition the whole vector into contiguous blocks
of size `2^(stage+1)`. -/
theorem layerGroupingSize (depth : Nat) (stage : Fin depth) :
    2 ^ (depth - stage.val - 1) * (2 * 2 ^ stage.val) = 2 ^ depth :=
  layerSize depth stage

private def layerPositionEquiv (depth : Nat) (stage : Fin depth) :
    LayerPosition depth stage ≃
      Fin (2 ^ (depth - stage.val - 1)) ×
        (Fin 2 × Fin (2 ^ stage.val)) where
  toFun position := (position.group, position.branch, position.offset)
  invFun position :=
    { group := position.1, branch := position.2.1, offset := position.2.2 }
  left_inv position := by cases position; rfl
  right_inv position := by rcases position with ⟨group, branch, offset⟩; rfl

/-- Interpret the group/branch/offset coordinates of a layer as a vector index.

The resulting index is
`offset + 2^stage * branch + 2^(stage+1) * group`.  Thus groups and branches
occupy contiguous ranges, while equal offsets in the two branches identify a
butterfly pair. -/
def layerIndexEquiv (depth : Nat) (stage : Fin depth) :
    LayerPosition depth stage ≃ Fin (2 ^ depth) :=
  (layerPositionEquiv depth stage).trans
    ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans
      (finProdFinEquiv.trans (finCongr (layerSize depth stage))))

@[simp]
theorem layerIndexEquiv_val (depth : Nat) (stage : Fin depth)
    (position : LayerPosition depth stage) :
    (layerIndexEquiv depth stage position).val =
      position.offset.val + 2 ^ stage.val * position.branch.val +
        (2 * 2 ^ stage.val) * position.group.val := by
  rfl

/-- The two inputs of one butterfly are separated by exactly `2^stage` vector
positions. -/
theorem layerIndexEquiv_pair_spacing (depth : Nat) (stage : Fin depth)
    (group : Fin (2 ^ (depth - stage.val - 1)))
    (offset : Fin (2 ^ stage.val)) :
    (layerIndexEquiv depth stage
        { group := group, branch := 1, offset := offset }).val =
      (layerIndexEquiv depth stage
        { group := group, branch := 0, offset := offset }).val +
        2 ^ stage.val := by
  simp only [layerIndexEquiv_val]
  omega

/-- One exact iterative radix-two butterfly layer.

Stage zero combines adjacent values.  Every later stage doubles both the
butterfly spacing and its contiguous group size.  The twiddle depends only on
the within-half `offset`: stage `s` uses the length-`2^(s+1)` twiddle at that
offset.  Branch zero receives the sum and branch one the difference. -/
noncomputable def butterflyLayer (depth : Nat) (stage : Fin depth)
    (input : Vector depth ℂ) : Vector depth ℂ :=
  fun outputIndex =>
    let position := (layerIndexEquiv depth stage).symm outputIndex
    let firstIndex := layerIndexEquiv depth stage { position with branch := 0 }
    let secondIndex := layerIndexEquiv depth stage { position with branch := 1 }
    let rotated :=
      twiddle (stage.val + 1)
          (halfIndexEquiv stage.val (Sum.inl position.offset)) *
        input secondIndex
    if position.branch = 0 then input firstIndex + rotated
    else input firstIndex - rotated

@[simp]
theorem butterflyLayer_first (depth : Nat) (stage : Fin depth)
    (input : Vector depth ℂ)
    (group : Fin (2 ^ (depth - stage.val - 1)))
    (offset : Fin (2 ^ stage.val)) :
    butterflyLayer depth stage input
        (layerIndexEquiv depth stage
          { group := group, branch := 0, offset := offset }) =
      input (layerIndexEquiv depth stage
          { group := group, branch := 0, offset := offset }) +
        twiddle (stage.val + 1)
            (halfIndexEquiv stage.val (Sum.inl offset)) *
          input (layerIndexEquiv depth stage
            { group := group, branch := 1, offset := offset }) := by
  simp [butterflyLayer]

@[simp]
theorem butterflyLayer_second (depth : Nat) (stage : Fin depth)
    (input : Vector depth ℂ)
    (group : Fin (2 ^ (depth - stage.val - 1)))
    (offset : Fin (2 ^ stage.val)) :
    butterflyLayer depth stage input
        (layerIndexEquiv depth stage
          { group := group, branch := 1, offset := offset }) =
      input (layerIndexEquiv depth stage
          { group := group, branch := 0, offset := offset }) -
        twiddle (stage.val + 1)
            (halfIndexEquiv stage.val (Sum.inl offset)) *
          input (layerIndexEquiv depth stage
            { group := group, branch := 1, offset := offset }) := by
  simp [butterflyLayer]

/-- Stages in execution order: `0, 1, ..., depth - 1`. -/
def butterflyStages (depth : Nat) : List (Fin depth) :=
  List.finRange depth

/-- A boundary between layers, represented by the number of completed stages.
The values range from zero through `depth`, inclusive. -/
abbrev LayerBoundary (depth : Nat) := Fin (depth + 1)

/-- The stages before a selected layer boundary. -/
def butterflyStagePrefix (depth : Nat) (boundary : LayerBoundary depth) :
    List (Fin depth) :=
  (butterflyStages depth).take boundary.val

/-- The stages at and after a selected layer boundary. -/
def butterflyStageSuffix (depth : Nat) (boundary : LayerBoundary depth) :
    List (Fin depth) :=
  (butterflyStages depth).drop boundary.val

/-- Advancing a boundary removes exactly the stage named by the old boundary
from the front of the remaining suffix. -/
theorem butterflyStageSuffix_castSucc (stage : Fin depth) :
    butterflyStageSuffix depth stage.castSucc =
      stage :: butterflyStageSuffix depth stage.succ := by
  simp [butterflyStageSuffix, butterflyStages, List.drop_eq_getElem_cons]

@[simp] theorem butterflyStagePrefix_final (depth : Nat) :
    butterflyStagePrefix depth (Fin.last depth) = butterflyStages depth := by
  unfold butterflyStagePrefix butterflyStages
  have stages : List.take (Fin.last depth).val (List.finRange depth) =
      List.finRange depth := by
    change List.take depth (List.finRange depth) = List.finRange depth
    simpa only [List.length_finRange] using
      (List.take_length (l := List.finRange depth))
  exact stages

/-- Advancing a boundary by one appends exactly the stage named by the old
boundary. -/
theorem butterflyStagePrefix_boundarySucc (stage : Fin depth) :
    butterflyStagePrefix depth stage.succ =
      butterflyStagePrefix depth stage.castSucc ++ [stage] := by
  simp [butterflyStagePrefix, butterflyStages, List.take_add_one]

/-- Apply an explicitly selected sequence of butterfly layers from left to
right.  Keeping the sequence explicit permits a later implementation to split
the same mathematical network into combinational and streamed portions. -/
noncomputable def applyButterflyLayers (depth : Nat)
    (stages : List (Fin depth)) (input : Vector depth ℂ) : Vector depth ℂ :=
  stages.foldl (fun current stage => butterflyLayer depth stage current) input

@[simp]
theorem applyButterflyLayers_nil (depth : Nat) (input : Vector depth ℂ) :
    applyButterflyLayers depth [] input = input :=
  rfl

theorem applyButterflyLayers_append (depth : Nat)
    (first second : List (Fin depth)) (input : Vector depth ℂ) :
    applyButterflyLayers depth (first ++ second) input =
      applyButterflyLayers depth second
        (applyButterflyLayers depth first input) := by
  simp [applyButterflyLayers, List.foldl_append]

/-- The exact hardware-shaped radix-two network: reverse the input index bits,
then apply stages from adjacent butterflies through full-vector butterflies.
The returned vector uses its ordinary index as the intended natural-frequency
output index; in particular, this definition performs no final permutation.
Its agreement with the recursive FFT is a separate theorem, not part of this
definition. -/
noncomputable def layeredFFT (depth : Nat) (input : Vector depth ℂ) :
    Vector depth ℂ :=
  applyButterflyLayers depth (butterflyStages depth) (bitReverse input)

/-- The exact state at a boundary in the layered network.  Boundary zero is
the bit-reversed input; boundary `depth` is the complete transform. -/
noncomputable def layeredPrefix (depth : Nat) (boundary : LayerBoundary depth)
    (input : Vector depth ℂ) : Vector depth ℂ :=
  applyButterflyLayers depth (butterflyStagePrefix depth boundary)
    (bitReverse input)

@[simp]
theorem layeredPrefix_zero (depth : Nat) (input : Vector depth ℂ) :
    layeredPrefix depth 0 input = bitReverse input :=
  rfl

@[simp]
theorem layeredPrefix_final (depth : Nat) (input : Vector depth ℂ) :
    layeredPrefix depth (Fin.last depth) input = layeredFFT depth input := by
  unfold layeredPrefix butterflyStagePrefix layeredFFT butterflyStages
  have stages : List.take (Fin.last depth).val (List.finRange depth) =
      List.finRange depth := by
    change List.take depth (List.finRange depth) = List.finRange depth
    simpa only [List.length_finRange] using
      (List.take_length (l := List.finRange depth))
  rw [stages]

/-- Advancing an exact prefix boundary applies exactly one additional layer. -/
theorem layeredPrefix_boundarySucc (stage : Fin depth)
    (input : Vector depth ℂ) :
    layeredPrefix depth stage.succ input =
      butterflyLayer depth stage
        (layeredPrefix depth stage.castSucc input) := by
  rw [layeredPrefix, butterflyStagePrefix_boundarySucc,
    applyButterflyLayers_append]
  rfl

/-- Splitting the layer sequence at any valid boundary preserves the complete
transform.  This is the pure theorem later used to assign the prefix and suffix
to different hardware organizations. -/
theorem layeredFFT_split (depth : Nat) (boundary : LayerBoundary depth)
    (input : Vector depth ℂ) :
    layeredFFT depth input =
      applyButterflyLayers depth (butterflyStageSuffix depth boundary)
        (layeredPrefix depth boundary input) := by
  rw [layeredFFT, ← List.take_append_drop boundary.val (butterflyStages depth),
    applyButterflyLayers_append]
  rfl

@[simp]
theorem layeredFFT_zero (input : Vector 0 ℂ) : layeredFFT 0 input = input := by
  funext index
  change input (bitReverseIndex index) = input index
  have reversedZero : bitReverseIndex index = 0 := Fin.eq_zero _
  have indexZero : index = 0 := Fin.eq_zero _
  exact congrArg input (reversedZero.trans indexZero.symm)

end HTFFT.Exact
