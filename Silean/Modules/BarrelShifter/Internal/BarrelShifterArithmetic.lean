import Silean.Modules.BarrelShifter.Internal.BarrelShifterStage
import Mathlib.Tactic

/-! Pure arithmetic of the logarithmic mux network. -/

namespace Silean.Modules.BarrelShifter.Internal

open Silean

/-- Shift word and data vector carried between pipeline stages. -/
abbrev Payload (element : SignalType) (exponent : Nat) :=
  (Fin exponent → Bool) × (Fin (size exponent) → element.Denote)

/-- Natural behavior of one complete pipeline stage, excluding its delay. -/
def stageFunction (exponent : Nat) (stage : Fin exponent)
    (payload : Payload element exponent) : Payload element exponent :=
  (payload.1,
    Level.resultValue exponent stage payload.1 payload.2)

/-- Stage indices completed at a selected boundary. -/
def stagePrefix (exponent : Nat) (boundary : Fin (exponent + 1)) :
    List (Fin exponent) :=
  (List.finRange exponent).take boundary.val

/-- Pure mux-network result at an intermediate stage boundary. -/
def boundaryResult (exponent : Nat) (boundary : Fin (exponent + 1))
    (payload : Payload element exponent) : Payload element exponent :=
  (payload.1,
    (stagePrefix exponent boundary).foldl
      (fun current stage =>
        Level.resultValue exponent stage payload.1 current) payload.2)

/-- Pipeline latency accumulated before an intermediate stage boundary. -/
def boundaryLatency (pipeline : Pipeline exponent)
    (boundary : Fin (exponent + 1)) : Nat :=
  ((stagePrefix exponent boundary).map fun stage =>
    (pipeline.registerBoundary stage.castSucc).toNat).sum

@[simp] theorem stagePrefix_zero (exponent : Nat) :
    stagePrefix exponent 0 = [] := by
  simp [stagePrefix]

@[simp] theorem stagePrefix_final (exponent : Nat) :
    stagePrefix exponent (Fin.last exponent) = List.finRange exponent := by
  unfold stagePrefix
  change List.take exponent (List.finRange exponent) = List.finRange exponent
  simpa only [List.length_finRange] using
    (List.take_length (l := List.finRange exponent))

/-- Advancing a boundary appends exactly its corresponding mux level. -/
theorem stagePrefix_boundarySucc (stage : Fin exponent) :
    stagePrefix exponent stage.succ =
      stagePrefix exponent stage.castSucc ++ [stage] := by
  simp [stagePrefix, List.take_add_one]

@[simp] theorem boundaryResult_zero (exponent : Nat) :
    boundaryResult (element := element) exponent 0 = id := by
  funext payload
  simp [boundaryResult]

/-- Advancing a boundary applies exactly one additional mux level. -/
theorem boundaryResult_succ (exponent : Nat) (stage : Fin exponent) :
    boundaryResult (element := element) exponent stage.succ =
      stageFunction exponent stage ∘
        boundaryResult (element := element) exponent stage.castSucc := by
  funext payload
  rcases payload with ⟨shift, input⟩
  simp [boundaryResult, stageFunction, stagePrefix_boundarySucc,
    List.foldl_append, Function.comp_apply]

@[simp] theorem boundaryLatency_zero (pipeline : Pipeline exponent) :
    boundaryLatency pipeline 0 = 0 := by
  simp [boundaryLatency]

/-- A stage contributes precisely its selected input-boundary register. -/
theorem boundaryLatency_succ (pipeline : Pipeline exponent)
    (stage : Fin exponent) :
    boundaryLatency pipeline stage.succ =
      boundaryLatency pipeline stage.castSucc +
        (pipeline.registerBoundary stage.castSucc).toNat := by
  simp [boundaryLatency, stagePrefix_boundarySucc]

/-- Nested left rotations add their amounts modulo the vector length. -/
theorem rotateValue_comp (exponent left right : Nat)
    (input : Fin (size exponent) → α) :
    rotateValue exponent right (rotateValue exponent left input) =
      rotateValue exponent (left + right) input := by
  funext output
  apply congrArg input
  apply Fin.ext
  change
    (((output.val + right) % size exponent + left) % size exponent) =
      ((output.val + (left + right)) % size exponent)
  simp [Nat.add_mod, Nat.add_comm, Nat.add_left_comm]

/-- The ascending finite range can equivalently be split at its final
element. -/
theorem finRange_castSucc_append_last : ∀ width : Nat,
    (List.finRange width).map Fin.castSucc ++ [Fin.last width] =
      List.finRange (width + 1)
  | width => by
      apply List.ext_getElem
      · simp
      · intro index leftBound rightBound
        simp only [List.getElem_finRange]
        by_cases beforeLast : index < width
        · rw [List.getElem_append_left (by simpa using beforeLast)]
          simp
        · have indexBound : index < width + 1 := by
            simpa using rightBound
          have atLast : index = width := by omega
          subst index
          rw [List.getElem_append_right (by simp [width])]
          simp [width]
          apply Fin.ext
          rfl

/-- The recursive bit-vector decoder is the sum of its selected binary
weights. -/
theorem toNat_eq_weightedSum : ∀ (width : Nat) (bits : Fin width → Bool),
    BitVector.toNat width bits =
      ((List.finRange width).map fun index =>
        if bits index then 2 ^ index.val else 0).sum
  | 0, bits => by simp [BitVector.toNat]
  | width + 1, bits => by
      rw [← finRange_castSucc_append_last width]
      simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [BitVector.toNat]
      rw [toNat_eq_weightedSum width (fun index => bits index.castSucc)]
      rw [BitVector.cardinality_eq_pow]
      calc
        _ =
            ((List.finRange width).map fun index =>
              if bits index.castSucc then 2 ^ index.val else 0).sum +
              (if bits (Fin.last width) then 2 ^ width else 0) :=
          Nat.add_comm _ _
        _ = _ := by
          congr 1

/-- Folding any list of mux levels produces one rotation by the sum of the
selected power-of-two amounts. -/
theorem foldStages_eq_rotate (exponent : Nat) (shift : Fin exponent → Bool)
    (stages : List (Fin exponent))
    (input : Fin (size exponent) → α) :
    stages.foldl
        (fun current stage =>
          Level.resultValue exponent stage shift current) input =
      rotateValue exponent
        ((stages.map fun stage =>
          if shift stage then 2 ^ stage.val else 0).sum) input := by
  induction stages generalizing input with
  | nil =>
      funext output
      change input output = input (rotateSourceIndex exponent 0 output)
      apply congrArg input
      apply Fin.ext
      exact (Nat.mod_eq_of_lt output.isLt).symm
  | cons stage stages induction =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [induction]
      by_cases selected : shift stage
      · simp only [Level.resultValue, selected, cond_true,
          Level.rotatedValue]
        rw [rotateValue_comp]
        congr 2
      · simp [Level.resultValue, selected]

/-- After all mux levels, the carried data is exactly the public natural
rotation and the shift word is unchanged. -/
theorem boundaryResult_final (exponent : Nat)
    (payload : Payload element exponent) :
    boundaryResult exponent (Fin.last exponent) payload =
      (payload.1, resultValue exponent payload.1 payload.2) := by
  rcases payload with ⟨shift, input⟩
  apply Prod.ext
  · rfl
  · change
      (stagePrefix exponent (Fin.last exponent)).foldl
        (fun current stage =>
          Level.resultValue exponent stage shift current) input = _
    rw [stagePrefix_final]
    rw [foldStages_eq_rotate]
    rw [← toNat_eq_weightedSum exponent shift]
    rfl

/-- All stage-boundary registers plus the final output register are exactly
the public pipeline latency. -/
theorem boundaryLatency_final_add_output (pipeline : Pipeline exponent) :
    boundaryLatency pipeline (Fin.last exponent) +
        (pipeline.registerBoundary (Fin.last exponent)).toNat =
      pipeline.latency := by
  unfold boundaryLatency Pipeline.latency
  rw [stagePrefix_final, ← finRange_castSucc_append_last exponent]
  simp only [List.map_append, List.map_map,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero]
  rfl

end Silean.Modules.BarrelShifter.Internal
