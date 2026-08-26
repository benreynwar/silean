import Silean2.Contracts.NoResetFifo

namespace Silean2.Contracts.NoResetFifo.Execution

structure Input (Word : Type) where
  enqValid : Bool
  enqData : Word
  deqReady : Bool

structure StepResult (State Word : Type) where
  nextState : State
  cycle : Cycle Word

structure RunResult (State Word : Type) where
  finalState : State
  cycles : List (Cycle Word)

structure Model (State Word : Type) where
  step : State → Input Word → StepResult State Word

namespace Model

def run (model : Model State Word) : State → List (Input Word) →
    RunResult State Word
  | state, [] => ⟨state, []⟩
  | state, input :: inputs =>
      let step := model.step state input
      let rest := model.run step.nextState inputs
      ⟨rest.finalState, step.cycle :: rest.cycles⟩

theorem run_conservation (model : Model State Word) (contents : State → List Word)
    (stepConservation : ∀ state input,
      contents state ++ (model.step state input).cycle.acceptedInput =
        (model.step state input).cycle.acceptedOutput ++
          contents (model.step state input).nextState) :
    ∀ initial inputs,
      contents initial ++ NoResetFifo.acceptedInputs
          (model.run initial inputs).cycles =
        NoResetFifo.acceptedOutputs (model.run initial inputs).cycles ++
          contents (model.run initial inputs).finalState := by
  intro initial inputs
  induction inputs generalizing initial with
  | nil => simp [run, NoResetFifo.acceptedInputs, NoResetFifo.acceptedOutputs]
  | cons input inputs induction =>
      simp only [run, NoResetFifo.acceptedInputs, NoResetFifo.acceptedOutputs]
      rw [← List.append_assoc, stepConservation]
      rw [List.append_assoc, induction]
      simp [List.append_assoc]

theorem run_ready_stalls_bound (model : Model State Word)
    (stepBound : ∀ state input,
      NoResetFifo.inputReadyStalls [(model.step state input).cycle] ≤
        NoResetFifo.outputReadyStalls [(model.step state input).cycle]) :
    ∀ initial inputs,
      NoResetFifo.inputReadyStalls (model.run initial inputs).cycles ≤
        NoResetFifo.outputReadyStalls (model.run initial inputs).cycles := by
  intro initial inputs
  induction inputs generalizing initial with
  | nil => simp [run, NoResetFifo.inputReadyStalls, NoResetFifo.outputReadyStalls]
  | cons input inputs induction =>
      simpa [run, NoResetFifo.inputReadyStalls, NoResetFifo.outputReadyStalls] using
        Nat.add_le_add (stepBound initial input)
          (induction (model.step initial input).nextState)

end Model

end Silean2.Contracts.NoResetFifo.Execution
