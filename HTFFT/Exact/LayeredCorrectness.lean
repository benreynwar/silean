import HTFFT.Exact.DFT
import HTFFT.Exact.Layered

namespace HTFFT.Exact

private theorem reverse_cons (bit : Bool) (bits : BitVec depth) :
    (BitVec.cons bit bits).reverse = BitVec.concat bits.reverse bit := by
  ext (_ | index) bound
  · simp [BitVec.getElem_reverse]
  · simp [BitVec.getElem_reverse]

private theorem ofFin_half_left (depth : Nat) (index : Fin (2 ^ depth)) :
    BitVec.ofFin (halfIndexEquiv depth (Sum.inl index)) =
      BitVec.cons false (BitVec.ofFin index) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofFin, BitVec.toNat_cons']
  simp [halfIndexEquiv]

private theorem ofFin_half_right (depth : Nat) (index : Fin (2 ^ depth)) :
    BitVec.ofFin (halfIndexEquiv depth (Sum.inr index)) =
      BitVec.cons true (BitVec.ofFin index) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofFin, BitVec.toNat_cons']
  simp only [halfIndexEquiv_right_val, Bool.toNat_true, BitVec.toNat_ofFin,
    Nat.shiftLeft_eq, one_mul]

private theorem ofFin_parity (depth : Nat) (index : Fin (2 ^ depth))
    (parity : Fin 2) :
    BitVec.ofFin (parityIndexEquiv depth (index, parity)) =
      BitVec.concat (BitVec.ofFin index) (parity = 1) := by
  apply BitVec.eq_of_toNat_eq
  fin_cases parity <;> simp [parityIndexEquiv, Nat.mul_comm, Nat.add_comm]

/-- Reversing an index in the lower half produces an even source index whose
remaining bits are the reversal of the within-half index. -/
theorem bitReverseIndex_half_left (depth : Nat) (index : Fin (2 ^ depth)) :
    bitReverseIndex (halfIndexEquiv depth (Sum.inl index)) =
      parityIndexEquiv depth (bitReverseIndex index, 0) := by
  unfold bitReverseIndex
  apply BitVec.toFin_inj.mpr
  rw [ofFin_half_left, reverse_cons, ofFin_parity]
  rfl

/-- Reversing an index in the upper half produces an odd source index whose
remaining bits are the reversal of the within-half index. -/
theorem bitReverseIndex_half_right (depth : Nat) (index : Fin (2 ^ depth)) :
    bitReverseIndex (halfIndexEquiv depth (Sum.inr index)) =
      parityIndexEquiv depth (bitReverseIndex index, 1) := by
  unfold bitReverseIndex
  apply BitVec.toFin_inj.mpr
  rw [ofFin_half_right, reverse_cons, ofFin_parity]
  rfl

/-- At one greater depth, bit reversal places the bit-reversed even inputs in
the first half and the bit-reversed odd inputs in the second half. -/
theorem bitReverse_eq_concatHalves (input : Vector (depth + 1) α) :
    bitReverse input =
      concatHalves (bitReverse (evens input)) (bitReverse (odds input)) := by
  funext outputIndex
  obtain ⟨half, rfl⟩ := (halfIndexEquiv depth).surjective outputIndex
  cases half with
  | inl index =>
      rw [concatHalves_first]
      simp only [bitReverse, evens_apply, bitReverseIndex_half_left]
  | inr index =>
      rw [concatHalves_second]
      simp only [bitReverse, odds_apply, bitReverseIndex_half_right]

/-- Splitting the groups of a nonfinal layer into two equal collections gives
the group count of that same layer at one greater vector depth. -/
theorem lowerLayerGroupCount (depth : Nat) (stage : Fin depth) :
    2 ^ ((depth - stage.val - 1) + 1) =
      2 ^ ((depth + 1) - stage.castSucc.val - 1) := by
  change 2 ^ ((depth - stage.val - 1) + 1) =
    2 ^ ((depth + 1) - stage.val - 1)
  congr 1
  omega

/-- Embedding a nonfinal stage into a larger transform does not change the
twiddle used at a shared within-group offset. -/
@[simp]
theorem lowerLayerTwiddle (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) :
    twiddle (stage.castSucc.val + 1)
        (halfIndexEquiv stage.castSucc.val (Sum.inl offset)) =
      twiddle (stage.val + 1)
        (halfIndexEquiv stage.val (Sum.inl offset)) :=
  rfl

/-- At the final stage of a depth-`depth + 1` transform, the layer twiddle is
exactly the recursive combine twiddle for the complete transform. -/
@[simp]
theorem finalLayerTwiddle (index : Fin (2 ^ depth)) :
    twiddle ((Fin.last depth).val + 1)
        (halfIndexEquiv (Fin.last depth).val (Sum.inl index)) =
      twiddle (depth + 1) (halfIndexEquiv depth (Sum.inl index)) :=
  rfl

/-- Embed a lower-depth layer position into the first half of the same stage
at one greater vector depth. -/
def LayerPosition.inFirstHalf (position : LayerPosition depth stage) :
    LayerPosition (depth + 1) stage.castSucc :=
  { group := Fin.cast (lowerLayerGroupCount depth stage)
      (halfIndexEquiv (depth - stage.val - 1) (Sum.inl position.group))
    branch := position.branch
    offset := position.offset }

/-- Embed a lower-depth layer position into the second half of the same stage
at one greater vector depth. -/
def LayerPosition.inSecondHalf (position : LayerPosition depth stage) :
    LayerPosition (depth + 1) stage.castSucc :=
  { group := Fin.cast (lowerLayerGroupCount depth stage)
      (halfIndexEquiv (depth - stage.val - 1) (Sum.inr position.group))
    branch := position.branch
    offset := position.offset }

/-- Embedding a layer position into the first group collection agrees with
embedding its vector index into the first half. -/
theorem layerIndex_inFirstHalf (position : LayerPosition depth stage) :
    layerIndexEquiv (depth + 1) stage.castSucc position.inFirstHalf =
      halfIndexEquiv depth (Sum.inl (layerIndexEquiv depth stage position)) := by
  apply Fin.ext
  simp [LayerPosition.inFirstHalf]

/-- Embedding a layer position into the second group collection agrees with
embedding its vector index into the second half. -/
theorem layerIndex_inSecondHalf (position : LayerPosition depth stage) :
    layerIndexEquiv (depth + 1) stage.castSucc position.inSecondHalf =
      halfIndexEquiv depth (Sum.inr (layerIndexEquiv depth stage position)) := by
  have blockSize : (2 * 2 ^ stage.val) * 2 ^ (depth - stage.val - 1) =
      2 ^ depth := by
    simpa [Nat.mul_comm] using layerGroupingSize depth stage
  apply Fin.ext
  simp [LayerPosition.inSecondHalf, Nat.mul_add, blockSize]
  omega

private theorem layerIndex_inFirstHalf_components
    (group : Fin (2 ^ (depth - stage.val - 1))) (branch : Fin 2)
    (offset : Fin (2 ^ stage.val)) :
    layerIndexEquiv (depth + 1) stage.castSucc
        { group := Fin.cast (lowerLayerGroupCount depth stage)
            (halfIndexEquiv (depth - stage.val - 1) (Sum.inl group))
          branch := branch
          offset := offset } =
      halfIndexEquiv depth (Sum.inl
        (layerIndexEquiv depth stage
          { group := group, branch := branch, offset := offset })) := by
  simpa only [LayerPosition.inFirstHalf] using
    layerIndex_inFirstHalf
      (position := ({ group := group, branch := branch, offset := offset } :
        LayerPosition depth stage))

private theorem layerIndex_inSecondHalf_components
    (group : Fin (2 ^ (depth - stage.val - 1))) (branch : Fin 2)
    (offset : Fin (2 ^ stage.val)) :
    layerIndexEquiv (depth + 1) stage.castSucc
        { group := Fin.cast (lowerLayerGroupCount depth stage)
            (halfIndexEquiv (depth - stage.val - 1) (Sum.inr group))
          branch := branch
          offset := offset } =
      halfIndexEquiv depth (Sum.inr
        (layerIndexEquiv depth stage
          { group := group, branch := branch, offset := offset })) := by
  simpa only [LayerPosition.inSecondHalf] using
    layerIndex_inSecondHalf
      (position := ({ group := group, branch := branch, offset := offset } :
        LayerPosition depth stage))

/-- Every nonfinal layer acts independently on the two halves of a vector.
This is the one-layer form of the prefix invariant. -/
theorem butterflyLayer_concatHalves (stage : Fin depth)
    (first second : Vector depth ℂ) :
    butterflyLayer (depth + 1) stage.castSucc (concatHalves first second) =
      concatHalves (butterflyLayer depth stage first)
        (butterflyLayer depth stage second) := by
  funext outputIndex
  obtain ⟨half, rfl⟩ := (halfIndexEquiv depth).surjective outputIndex
  cases half with
  | inl localIndex =>
      rw [concatHalves_first]
      obtain ⟨position, rfl⟩ := (layerIndexEquiv depth stage).surjective localIndex
      rw [← layerIndex_inFirstHalf]
      rcases position with ⟨group, branch, offset⟩
      by_cases branchZero : branch = 0
      · subst branch
        simp only [LayerPosition.inFirstHalf]
        rw [butterflyLayer_first, butterflyLayer_first]
        rw [layerIndex_inFirstHalf_components, layerIndex_inFirstHalf_components]
        rw [concatHalves_first, concatHalves_first]
        rfl
      · have branchOne : branch = 1 := by apply Fin.ext; omega
        subst branch
        simp only [LayerPosition.inFirstHalf]
        rw [butterflyLayer_second, butterflyLayer_second]
        rw [layerIndex_inFirstHalf_components, layerIndex_inFirstHalf_components]
        rw [concatHalves_first, concatHalves_first]
        rfl
  | inr localIndex =>
      rw [concatHalves_second]
      obtain ⟨position, rfl⟩ := (layerIndexEquiv depth stage).surjective localIndex
      rw [← layerIndex_inSecondHalf]
      rcases position with ⟨group, branch, offset⟩
      by_cases branchZero : branch = 0
      · subst branch
        simp only [LayerPosition.inSecondHalf]
        rw [butterflyLayer_first, butterflyLayer_first]
        rw [layerIndex_inSecondHalf_components, layerIndex_inSecondHalf_components]
        rw [concatHalves_second, concatHalves_second]
        rfl
      · have branchOne : branch = 1 := by apply Fin.ext; omega
        subst branch
        simp only [LayerPosition.inSecondHalf]
        rw [butterflyLayer_second, butterflyLayer_second]
        rw [layerIndex_inSecondHalf_components, layerIndex_inSecondHalf_components]
        rw [concatHalves_second, concatHalves_second]
        rfl

/-- Any sequence of nonfinal layers preserves the two-half decomposition and
applies the corresponding lower-depth layers independently.  In particular,
this describes every prefix that stops before the final layer. -/
theorem applyButterflyLayers_concatHalves (stages : List (Fin depth))
    (first second : Vector depth ℂ) :
    applyButterflyLayers (depth + 1) (stages.map Fin.castSucc)
        (concatHalves first second) =
      concatHalves (applyButterflyLayers depth stages first)
        (applyButterflyLayers depth stages second) := by
  induction stages generalizing first second with
  | nil => rfl
  | cons stage stages inductionHypothesis =>
      simp only [List.map_cons, applyButterflyLayers, List.foldl_cons]
      rw [butterflyLayer_concatHalves]
      exact inductionHypothesis _ _

/-- In the final layer, branch zero is the first half of the vector. -/
theorem finalLayerIndex_first (index : Fin (2 ^ depth)) :
    layerIndexEquiv (depth + 1) (Fin.last depth)
        { group := 0, branch := 0, offset := index } =
      halfIndexEquiv depth (Sum.inl index) := by
  apply Fin.ext
  simp

/-- In the final layer, branch one is the second half of the vector. -/
theorem finalLayerIndex_second (index : Fin (2 ^ depth)) :
    layerIndexEquiv (depth + 1) (Fin.last depth)
        { group := 0, branch := 1, offset := index } =
      halfIndexEquiv depth (Sum.inr index) := by
  apply Fin.ext
  simp
  omega

/-- The final layer combines two already-transformed halves with exactly the
same twiddle, sum, difference, and output placement as the recursive FFT. -/
theorem butterflyLayer_final (first second : Vector depth ℂ) :
    butterflyLayer (depth + 1) (Fin.last depth)
        (concatHalves first second) =
      concatHalves
        (fun index => first index +
          twiddle (depth + 1) (halfIndexEquiv depth (Sum.inl index)) *
            second index)
        (fun index => first index -
          twiddle (depth + 1) (halfIndexEquiv depth (Sum.inl index)) *
            second index) := by
  funext outputIndex
  obtain ⟨half, rfl⟩ := (halfIndexEquiv depth).surjective outputIndex
  cases half with
  | inl index =>
      rw [concatHalves_first, ← finalLayerIndex_first]
      rw [butterflyLayer_first]
      rw [finalLayerIndex_first, finalLayerIndex_second]
      rw [concatHalves_first, concatHalves_second]
      rfl
  | inr index =>
      rw [concatHalves_second, ← finalLayerIndex_second]
      rw [butterflyLayer_second]
      rw [finalLayerIndex_first, finalLayerIndex_second]
      rw [concatHalves_first, concatHalves_second]
      rfl

/-- The stage list at successor depth consists of all lower-depth stages,
embedded without changing their numbers, followed by the new final stage. -/
theorem butterflyStages_succ (depth : Nat) :
    butterflyStages (depth + 1) =
      (butterflyStages depth).map Fin.castSucc ++ [Fin.last depth] := by
  apply List.ext_getElem
  · simp [butterflyStages]
  · intro index leftBound rightBound
    simp only [butterflyStages, List.getElem_finRange]
    by_cases beforeLast : index < depth
    · simp [beforeLast]
    · have atLast : index = depth := by
        have indexBound : index < depth + 1 := by
          simpa [butterflyStages] using leftBound
        omega
      subst index
      simp
      apply Fin.ext
      rfl

/-- A nonfinal prefix at successor depth is the corresponding lower-depth
prefix embedded into the larger stage type. -/
theorem butterflyStagePrefix_succ (depth : Nat)
    (boundary : LayerBoundary depth) :
    butterflyStagePrefix (depth + 1) boundary.castSucc =
      (butterflyStagePrefix depth boundary).map Fin.castSucc := by
  unfold butterflyStagePrefix
  rw [butterflyStages_succ]
  rw [List.take_append_of_le_length]
  · exact List.map_take.symm
  · rw [List.length_map]
    change boundary.val ≤ (butterflyStages depth).length
    rw [show (butterflyStages depth).length = depth by simp [butterflyStages]]
    omega

/-- Semantic prefix invariant: before the final layer, the larger network is
exactly two independent lower-depth prefixes over the even and odd inputs. -/
theorem layeredPrefix_succ (input : Vector (depth + 1) ℂ)
    (boundary : LayerBoundary depth) :
    layeredPrefix (depth + 1) boundary.castSucc input =
      concatHalves (layeredPrefix depth boundary (evens input))
        (layeredPrefix depth boundary (odds input)) := by
  rw [layeredPrefix, butterflyStagePrefix_succ]
  rw [bitReverse_eq_concatHalves]
  rw [applyButterflyLayers_concatHalves]
  rfl

/-- The complete layered network obeys the same one-step recursive equation as
the exact recursive radix-two FFT. -/
theorem layeredFFT_succ (input : Vector (depth + 1) ℂ) :
    layeredFFT (depth + 1) input =
      concatHalves
        (fun index => layeredFFT depth (evens input) index +
          twiddle (depth + 1) (halfIndexEquiv depth (Sum.inl index)) *
            layeredFFT depth (odds input) index)
        (fun index => layeredFFT depth (evens input) index -
          twiddle (depth + 1) (halfIndexEquiv depth (Sum.inl index)) *
            layeredFFT depth (odds input) index) := by
  rw [layeredFFT, butterflyStages_succ, applyButterflyLayers_append]
  rw [bitReverse_eq_concatHalves]
  rw [applyButterflyLayers_concatHalves]
  change butterflyLayer (depth + 1) (Fin.last depth)
    (concatHalves
      (applyButterflyLayers depth (butterflyStages depth)
        (bitReverse (evens input)))
      (applyButterflyLayers depth (butterflyStages depth)
        (bitReverse (odds input)))) = _
  rw [butterflyLayer_final]
  rfl

/-- The bit-reversed layered network and the recursive radix-two FFT are equal
as exact complex-valued functions. -/
theorem layeredFFT_eq_radix2 (depth : Nat) (input : Vector depth ℂ) :
    layeredFFT depth input = radix2 depth input := by
  induction depth with
  | zero =>
      rw [layeredFFT_zero]
      rfl
  | succ depth inductionHypothesis =>
      rw [layeredFFT_succ, radix2]
      congr 1 <;> funext index <;>
        rw [inductionHypothesis, inductionHypothesis]

/-- The exact layered network computes Mathlib's unnormalized,
negative-exponent `ZMod.dft` in natural frequency order. -/
theorem layeredFFT_agreesWithDFT (depth : Nat) (input : Vector depth ℂ)
    (index : Fin (2 ^ depth)) :
    layeredFFT depth input index =
      ZMod.dft (toZModVector input) (zmodIndexEquiv depth index) := by
  rw [layeredFFT_eq_radix2, radix2_agreesWithDFT]

end HTFFT.Exact
