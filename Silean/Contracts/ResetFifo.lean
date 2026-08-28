import Silean.Contracts.NoResetFifo
import Silean.Foundation.Execution

namespace Silean.Contracts.ResetFifo

structure Cycle (Word : Type) extends NoResetFifo.Cycle Word where
  reset : Bool

def Cycle.acceptedInput (cycle : Cycle Word) : List Word :=
  bif cycle.reset then [] else cycle.toCycle.acceptedInput

def Cycle.acceptedOutput (cycle : Cycle Word) : List Word :=
  bif cycle.reset then [] else cycle.toCycle.acceptedOutput

def Step (current : List Word) (cycle : Cycle Word) (next : List Word) : Prop :=
  if cycle.reset then next = []
  else current ++ cycle.acceptedInput = cycle.acceptedOutput ++ next

inductive Transitions : List Word → List (Cycle Word) → List Word → Prop
  | nil (contents) : Transitions contents [] contents
  | cons {current middle final cycle cycles} :
      Step current cycle middle →
      Transitions middle cycles final →
      Transitions current (cycle :: cycles) final

def acceptedInputs : List (Cycle Word) → List Word
  | [] => []
  | cycle :: cycles => cycle.acceptedInput ++ acceptedInputs cycles

def acceptedOutputs : List (Cycle Word) → List Word
  | [] => []
  | cycle :: cycles => cycle.acceptedOutput ++ acceptedOutputs cycles

@[simp] theorem acceptedInput_of_reset (cycle : Cycle Word)
    (reset : cycle.reset = true) : cycle.acceptedInput = [] := by
  simp [Cycle.acceptedInput, reset]

@[simp] theorem acceptedOutput_of_reset (cycle : Cycle Word)
    (reset : cycle.reset = true) : cycle.acceptedOutput = [] := by
  simp [Cycle.acceptedOutput, reset]

theorem Step.reset {current next : List Word} {cycle : Cycle Word}
    (reset : cycle.reset = true) (step : Step current cycle next) : next = [] := by
  simpa [Step, reset] using step

theorem Step.ordinary {current next : List Word} {cycle : Cycle Word}
    (notReset : cycle.reset = false) (step : Step current cycle next) :
    current ++ cycle.acceptedInput = cycle.acceptedOutput ++ next := by
  simpa [Step, notReset] using step

theorem Transitions.conservation_without_reset
    (transitions : Transitions initial cycles final)
    (ordinary : ∀ cycle, cycle ∈ cycles → cycle.reset = false) :
    initial ++ acceptedInputs cycles = acceptedOutputs cycles ++ final := by
  induction transitions with
  | nil => simp [acceptedInputs, acceptedOutputs]
  | @cons current middle final cycle cycles step rest induction =>
      have cycleOrdinary := ordinary cycle (by simp)
      have restOrdinary : ∀ item, item ∈ cycles → item.reset = false := by
        intro item member
        exact ordinary item (by simp [member])
      simp only [acceptedInputs, acceptedOutputs]
      rw [← List.append_assoc, step.ordinary cycleOrdinary]
      rw [List.append_assoc, induction restOrdinary]
      simp [List.append_assoc]

theorem Transitions.outputs_prefix_inputs_of_empty
    (transitions : Transitions [] cycles final)
    (ordinary : ∀ cycle, cycle ∈ cycles → cycle.reset = false) :
    (acceptedOutputs cycles).IsPrefix (acceptedInputs cycles) := by
  apply List.prefix_iff_exists_append_eq.mpr
  refine ⟨final, ?_⟩
  simpa using (transitions.conservation_without_reset ordinary).symm

namespace Execution

structure Input (Word : Type) where
  enqValid : Bool
  enqData : Word
  deqReady : Bool
  reset : Bool

abbrev StepResult (State Word : Type) :=
  Silean.Execution.StepResult State (Cycle Word)

abbrev Model (State Word : Type) :=
  Silean.Execution.Model State (Input Word) (Cycle Word)

namespace Model

theorem run_correct (model : Model State Word) (valid : State → Prop)
    (contents : State → List Word)
    (stepValid : ∀ state input, valid state →
      valid (model.step state input).nextState)
    (stepCorrect : ∀ state input, valid state →
      Step (contents state) (model.step state input).observation
        (contents (model.step state input).nextState)) :
    ∀ initial inputs, valid initial →
      valid (model.run initial inputs).finalState ∧
      Transitions (contents initial) (model.run initial inputs).observations
        (contents (model.run initial inputs).finalState) := by
  intro initial inputs initialValid
  induction inputs generalizing initial with
  | nil => exact ⟨initialValid, Transitions.nil _⟩
  | cons input inputs induction =>
      let first := model.step initial input
      have nextValid : valid first.nextState := stepValid initial input initialValid
      rcases induction first.nextState nextValid with ⟨finalValid, restCorrect⟩
      exact ⟨finalValid,
        Transitions.cons (stepCorrect initial input initialValid) restCorrect⟩

end Model

end Execution

end Silean.Contracts.ResetFifo
