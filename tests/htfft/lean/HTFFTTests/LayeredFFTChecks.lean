import HTFFT.Exact.LayeredCorrectness

namespace HTFFTTests.LayeredFFT

open HTFFT.Exact

def layerPositions (depth : Nat) (stage : Fin depth) :
    List (Nat × Nat × Nat) :=
  List.ofFn fun index =>
    let position := (layerIndexEquiv depth stage).symm index
    (position.group.val, position.branch.val, position.offset.val)

-- Layers execute from adjacent pairs toward progressively larger blocks.
#guard (butterflyStages 0).map Fin.val == []
#guard (butterflyStages 1).map Fin.val == [0]
#guard (butterflyStages 2).map Fin.val == [0, 1]
#guard (butterflyStages 3).map Fin.val == [0, 1, 2]

-- Every valid boundary partitions that ordered list into a prefix and suffix.
#guard (butterflyStagePrefix 3 0).map Fin.val == []
#guard (butterflyStageSuffix 3 0).map Fin.val == [0, 1, 2]
#guard (butterflyStagePrefix 3 1).map Fin.val == [0]
#guard (butterflyStageSuffix 3 1).map Fin.val == [1, 2]
#guard (butterflyStagePrefix 3 2).map Fin.val == [0, 1]
#guard (butterflyStageSuffix 3 2).map Fin.val == [2]
#guard (butterflyStagePrefix 3 3).map Fin.val == [0, 1, 2]
#guard (butterflyStageSuffix 3 3).map Fin.val == []

-- A stage-zero layer pairs adjacent positions in each contiguous group.
#guard layerPositions 1 0 == [(0, 0, 0), (0, 1, 0)]
#guard layerPositions 2 0 ==
  [(0, 0, 0), (0, 1, 0), (1, 0, 0), (1, 1, 0)]
#guard layerPositions 3 0 ==
  [(0, 0, 0), (0, 1, 0), (1, 0, 0), (1, 1, 0),
   (2, 0, 0), (2, 1, 0), (3, 0, 0), (3, 1, 0)]

-- Later layers double the spacing while retaining contiguous groups.
#guard layerPositions 2 1 ==
  [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1)]
#guard layerPositions 3 1 ==
  [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1),
   (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1)]
#guard layerPositions 3 2 ==
  [(0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 0, 3),
   (0, 1, 0), (0, 1, 1), (0, 1, 2), (0, 1, 3)]

-- Depth zero has no butterfly layer and bit reversal is the identity.
example (input : Vector 0 ℂ) : layeredFFT 0 input = input := by
  exact layeredFFT_zero input

-- At depth one the complete network is exactly one sum/difference butterfly.
example (input : Vector 1 ℂ) :
    layeredFFT 1 input 0 = input 0 + input 1 := by
  have reversed : bitReverse input = input := by
    funext index
    fin_cases index <;> rfl
  rw [show layeredFFT 1 input = butterflyLayer 1 0 (bitReverse input) by rfl,
    reversed]
  rw [show (0 : Fin 2) = layerIndexEquiv 1 0
    { group := 0, branch := 0, offset := 0 } by decide]
  rw [butterflyLayer_first]
  rw [show layerIndexEquiv 1 0
      { group := 0, branch := 0, offset := 0 } = (0 : Fin 2) by decide]
  rw [show layerIndexEquiv 1 0
      { group := 0, branch := 1, offset := 0 } = (1 : Fin 2) by decide]
  change input 0 + twiddle 1 0 * input 1 = _
  simp

example (input : Vector 1 ℂ) :
    layeredFFT 1 input 1 = input 0 - input 1 := by
  have reversed : bitReverse input = input := by
    funext index
    fin_cases index <;> rfl
  rw [show layeredFFT 1 input = butterflyLayer 1 0 (bitReverse input) by rfl,
    reversed]
  rw [show (1 : Fin 2) = layerIndexEquiv 1 0
    { group := 0, branch := 1, offset := 0 } by decide]
  rw [butterflyLayer_second]
  rw [show layerIndexEquiv 1 0
      { group := 0, branch := 0, offset := 0 } = (0 : Fin 2) by decide]
  rw [show layerIndexEquiv 1 0
      { group := 0, branch := 1, offset := 0 } = (1 : Fin 2) by decide]
  change input 0 - twiddle 1 0 * input 1 = _
  simp

def ones (depth : Nat) : Vector depth ℂ := fun _ => 1

private theorem butterflyLayer_first_zero (depth : Nat) (stage : Fin depth)
    (input : Vector depth ℂ)
    (group : Fin (2 ^ (depth - stage.val - 1))) :
    butterflyLayer depth stage input
        (layerIndexEquiv depth stage
          { group := group, branch := 0, offset := 0 }) =
      input (layerIndexEquiv depth stage
          { group := group, branch := 0, offset := 0 }) +
        input (layerIndexEquiv depth stage
          { group := group, branch := 1, offset := 0 }) := by
  rw [butterflyLayer_first]
  have zeroIndex :
      halfIndexEquiv stage.val (Sum.inl (0 : Fin (2 ^ stage.val))) =
        (0 : Fin (2 ^ (stage.val + 1))) := by
    apply Fin.ext
    rfl
  rw [zeroIndex, twiddle_zero]
  simp

-- The offset-zero pair at depths two and three uses twiddle one.  These checks
-- exercise the exact arithmetic as well as the widening butterfly spacing.
example : butterflyLayer 2 1 (ones 2)
      (layerIndexEquiv 2 1 { group := 0, branch := 0, offset := 0 }) = 2 := by
  rw [butterflyLayer_first]
  change (1 : ℂ) + twiddle 2 0 * 1 = 2
  norm_num

example : butterflyLayer 2 1 (ones 2)
      (layerIndexEquiv 2 1 { group := 0, branch := 1, offset := 0 }) = 0 := by
  rw [butterflyLayer_second]
  change (1 : ℂ) - twiddle 2 0 * 1 = 0
  simp

example : butterflyLayer 3 2 (ones 3)
      (layerIndexEquiv 3 2 { group := 0, branch := 0, offset := 0 }) = 2 := by
  rw [butterflyLayer_first]
  change (1 : ℂ) + twiddle 3 0 * 1 = 2
  norm_num

example : butterflyLayer 3 2 (ones 3)
      (layerIndexEquiv 3 2 { group := 0, branch := 1, offset := 0 }) = 0 := by
  rw [butterflyLayer_second]
  change (1 : ℂ) - twiddle 3 0 * 1 = 0
  simp

-- Following the complete layer chain, a constant signal accumulates at the
-- intended natural-order DC output.  These proofs use only the layered model.
example : layeredFFT 2 (ones 2) 0 = 4 := by
  change butterflyLayer 2 1 (butterflyLayer 2 0 (bitReverse (ones 2))) 0 = 4
  have reversed : bitReverse (ones 2) = ones 2 := by
    funext index
    rfl
  rw [reversed]
  rw [show (0 : Fin 4) = layerIndexEquiv 2 1
      { group := 0, branch := 0, offset := 0 } by decide,
    butterflyLayer_first_zero]
  rw [show layerIndexEquiv 2 1
      { group := 0, branch := 0, offset := 0 } = (0 : Fin 4) by decide,
    show layerIndexEquiv 2 1
      { group := 0, branch := 1, offset := 0 } = (2 : Fin 4) by decide]
  rw [show (0 : Fin 4) = layerIndexEquiv 2 0
      { group := 0, branch := 0, offset := 0 } by decide,
    butterflyLayer_first_zero]
  rw [show (2 : Fin 4) = layerIndexEquiv 2 0
      { group := 1, branch := 0, offset := 0 } by decide,
    butterflyLayer_first_zero]
  norm_num [ones]

example : layeredFFT 3 (ones 3) 0 = 8 := by
  change butterflyLayer 3 2
    (butterflyLayer 3 1 (butterflyLayer 3 0 (bitReverse (ones 3)))) 0 = 8
  have reversed : bitReverse (ones 3) = ones 3 := by
    funext index
    rfl
  rw [reversed]
  rw [show (0 : Fin 8) = layerIndexEquiv 3 2
      { group := 0, branch := 0, offset := 0 } by decide,
    butterflyLayer_first_zero]
  rw [show layerIndexEquiv 3 2
      { group := 0, branch := 0, offset := 0 } = (0 : Fin 8) by decide,
    show layerIndexEquiv 3 2
      { group := 0, branch := 1, offset := 0 } = (4 : Fin 8) by decide]
  rw [show (0 : Fin 8) = layerIndexEquiv 3 1
      { group := 0, branch := 0, offset := 0 } by decide,
    butterflyLayer_first_zero]
  rw [show (4 : Fin 8) = layerIndexEquiv 3 1
      { group := 1, branch := 0, offset := 0 } by decide,
    butterflyLayer_first_zero]
  rw [show layerIndexEquiv 3 1
      { group := 0, branch := 0, offset := 0 } = (0 : Fin 8) by decide,
    show layerIndexEquiv 3 1
      { group := 0, branch := 1, offset := 0 } = (2 : Fin 8) by decide,
    show layerIndexEquiv 3 1
      { group := 1, branch := 0, offset := 0 } = (4 : Fin 8) by decide,
    show layerIndexEquiv 3 1
      { group := 1, branch := 1, offset := 0 } = (6 : Fin 8) by decide]
  rw [show (0 : Fin 8) = layerIndexEquiv 3 0
      { group := 0, branch := 0, offset := 0 } by decide,
    butterflyLayer_first_zero]
  rw [show (2 : Fin 8) = layerIndexEquiv 3 0
      { group := 1, branch := 0, offset := 0 } by decide,
    butterflyLayer_first_zero]
  rw [show (4 : Fin 8) = layerIndexEquiv 3 0
      { group := 2, branch := 0, offset := 0 } by decide,
    butterflyLayer_first_zero]
  rw [show (6 : Fin 8) = layerIndexEquiv 3 0
      { group := 3, branch := 0, offset := 0 } by decide,
    butterflyLayer_first_zero]
  norm_num [ones]

-- A two-stage prefix of the eight-point network is exactly two independent
-- complete four-point networks over the even and odd inputs.
example (input : Vector 3 ℂ) :
    layeredPrefix 3 (Fin.castSucc (Fin.last 2)) input =
      concatHalves (layeredFFT 2 (evens input))
        (layeredFFT 2 (odds input)) := by
  have hPrefix := layeredPrefix_succ (depth := 2) input (Fin.last 2)
  rw [layeredPrefix_final, layeredPrefix_final] at hPrefix
  exact hPrefix

def impulse (depth : Nat) : Vector depth ℂ :=
  fun index => if index = 0 then 1 else 0

private theorem layeredFFT_impulse (depth : Nat) (index : Fin (2 ^ depth)) :
    layeredFFT depth (impulse depth) index = 1 := by
  rw [layeredFFT_agreesWithDFT, dft_eq_sum_fourierCoefficient]
  simp [impulse, fourierCoefficient]

-- The final correctness theorem is exercised at every small depth used by the
-- indexing checks, including the length-one base case.
example : layeredFFT 0 (impulse 0) = fun _ => 1 := by
  funext index
  exact layeredFFT_impulse 0 index

example : layeredFFT 1 (impulse 1) = fun _ => 1 := by
  funext index
  exact layeredFFT_impulse 1 index

example : layeredFFT 2 (impulse 2) = fun _ => 1 := by
  funext index
  exact layeredFFT_impulse 2 index

example : layeredFFT 3 (impulse 3) = fun _ => 1 := by
  funext index
  exact layeredFFT_impulse 3 index

-- An implementation may split the ordered layers at any boundary without
-- changing their mathematical composition.
#check applyButterflyLayers_append
#check layeredFFT_split
#check layeredPrefix_succ
#check layeredFFT_eq_radix2
#check layeredFFT_agreesWithDFT

end HTFFTTests.LayeredFFT
