import HTFFT.Silean.FFTStage.Internal.FFTStageScheduleCorrectness

namespace HTFFTTests.FFTStageSchedule

open HTFFT.Silean.FFTStage.Internal

private def initial : Commutator.State 2 Nat where
  -- Deliberately misaligned: the marker must override this phase immediately.
  phase := ⟨3, by decide⟩
  outputPhase := ⟨2, by decide⟩
  markerDelay := fun _ => false
  firstDelay := fun index => 900 + index.val
  secondDelay := fun index => 950 + index.val

private def inputs : List (Commutator.Input Nat) :=
  (List.range 8).map fun cycle =>
    { first := cycle == 0
      a := 10 + cycle
      b := 20 + cycle }

private def relevantOutputs : List (Commutator.Operands Nat) :=
  (Commutator.run 2 (by decide) initial inputs).1.drop 2

-- After the unconstrained two-cycle fill, the low-half pairs are followed by
-- the high-half pairs, and then the schedule repeats for the next local group.
#guard relevantOutputs == [
  { a := 10, b := 12 },
  { a := 11, b := 13 },
  { a := 20, b := 22 },
  { a := 21, b := 23 },
  { a := 14, b := 16 },
  { a := 15, b := 17 }]

example (stored : Fin 4) :
    Commutator.effectivePhase 2 (by decide) stored true = 0 := by
  rfl

example (stored : Fin 4) :
    Commutator.nextPhase 2 (by decide) stored true = 1 := by
  rfl

private def bankInitial : CommutatorBank.State 2 2 Nat :=
  fun lane =>
    { phase := ⟨lane.val + 2, by omega⟩
      outputPhase := ⟨3 - lane.val, by omega⟩
      markerDelay := fun index => index.val == lane.val
      firstDelay := fun index => 800 + 10 * lane.val + index.val
      secondDelay := fun index => 900 + 10 * lane.val + index.val }

private def bankFrame : Fin 8 → CommutatorBank.Input 2 Nat :=
  fun cycle =>
    { first := cycle.val == 0
      a := fun lane => 100 * lane.val + 10 + cycle.val
      b := fun lane => 100 * lane.val + 20 + cycle.val }

private def bankContinuation : Fin 2 → CommutatorBank.Input 2 Nat :=
  fun cycle =>
    { -- A following frame may start while the preceding frame's tail emerges.
      first := cycle.val == 0
      a := fun lane => 1000 + 100 * lane.val + cycle.val
      b := fun lane => 2000 + 100 * lane.val + cycle.val }

private def bankLaneZeroOutputs : List (Commutator.Operands Nat) :=
  List.ofFn fun cycle : Fin 8 =>
    (CommutatorBank.frameSignal 2 2 (by decide) bankInitial bankFrame
      bankContinuation cycle 0).operands

private def bankLaneZeroPhases : List Nat :=
  List.ofFn fun cycle : Fin 8 =>
    (CommutatorBank.frameSignal 2 2 (by decide) bankInitial bankFrame
      bankContinuation cycle 0).outputPhase.val

-- The complete two-period frame is independent of arbitrary initial phase and
-- delay contents.  The continuation marker also leaves the previous tail
-- untouched.
#guard bankLaneZeroOutputs == [
  { a := 10, b := 12 },
  { a := 11, b := 13 },
  { a := 20, b := 22 },
  { a := 21, b := 23 },
  { a := 14, b := 16 },
  { a := 15, b := 17 },
  { a := 24, b := 26 },
  { a := 25, b := 27 }]

#guard bankLaneZeroPhases == [0, 1, 2, 3, 0, 1, 2, 3]

example : Silean.FramedLatency.Starts (by decide)
    (fun input : CommutatorBank.Input 2 Nat => input.first = true)
    bankFrame := by
  constructor
  · decide
  · intro offset nonzero
    simpa [bankFrame] using nonzero

-- Keep the strongest reusable pure-stage theorem visible at the test boundary.
#check outputFrameOfBankFrameSignals_eq_contractResult

end HTFFTTests.FFTStageSchedule
