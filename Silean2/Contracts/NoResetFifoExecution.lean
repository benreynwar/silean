import Silean2.Contracts.NoResetFifo
import Silean2.Foundation.Execution

namespace Silean2.Contracts.NoResetFifo.Execution

structure Input (Word : Type) where
  enqValid : Bool
  enqData : Word
  deqReady : Bool

abbrev StepResult (State Word : Type) :=
  Silean2.Execution.StepResult State (Cycle Word)

abbrev Model (State Word : Type) :=
  Silean2.Execution.Model State (Input Word) (Cycle Word)

namespace Model

theorem run_conservation (model : Model State Word) (contents : State → List Word)
    (stepConservation : ∀ state input,
      contents state ++ (model.step state input).observation.acceptedInput =
        (model.step state input).observation.acceptedOutput ++
          contents (model.step state input).nextState) :
    ∀ initial inputs,
      contents initial ++ NoResetFifo.acceptedInputs
          (model.run initial inputs).observations =
        NoResetFifo.acceptedOutputs (model.run initial inputs).observations ++
          contents (model.run initial inputs).finalState := by
  intro initial inputs
  induction inputs generalizing initial with
  | nil => simp [Silean2.Execution.Model.run, NoResetFifo.acceptedInputs,
      NoResetFifo.acceptedOutputs]
  | cons input inputs induction =>
      simp only [Silean2.Execution.Model.run, NoResetFifo.acceptedInputs,
        NoResetFifo.acceptedOutputs]
      rw [← List.append_assoc, stepConservation]
      rw [List.append_assoc, induction]
      simp [List.append_assoc]

theorem run_ready_stalls_bound (model : Model State Word)
    (stepBound : ∀ state input,
      NoResetFifo.inputReadyStalls [(model.step state input).observation] ≤
        NoResetFifo.outputReadyStalls [(model.step state input).observation]) :
    ∀ initial inputs,
      NoResetFifo.inputReadyStalls (model.run initial inputs).observations ≤
        NoResetFifo.outputReadyStalls (model.run initial inputs).observations := by
  intro initial inputs
  induction inputs generalizing initial with
  | nil => simp [Silean2.Execution.Model.run, NoResetFifo.inputReadyStalls,
      NoResetFifo.outputReadyStalls]
  | cons input inputs induction =>
      simpa [Silean2.Execution.Model.run, NoResetFifo.inputReadyStalls,
        NoResetFifo.outputReadyStalls] using
        Nat.add_le_add (stepBound initial input)
          (induction (model.step initial input).nextState)

end Model

end Silean2.Contracts.NoResetFifo.Execution
