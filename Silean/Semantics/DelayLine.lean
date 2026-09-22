import Silean.Semantics.Trace

/-! # Delay-line traces

This file gives the small temporal lemma shared by hardware built from chains
of ordinary registers. It is independent of module structure and contracts.
-/

namespace Silean.DelayLine

/-- One abstract shift of a delay line. Index zero is the value observed at
the output; increasing indices move toward the input. At latency zero the
input is observed directly. -/
def Step (latency : Nat) (input : α) (currentState : Fin latency → α)
    (output : α) (nextState : Fin latency → α) : Prop :=
  output = (if positive : 0 < latency then currentState ⟨0, positive⟩ else input) ∧
  ∀ index, nextState index =
    if earlier : index.val + 1 < latency then
      currentState ⟨index.val + 1, earlier⟩
    else
      input

/-- A value already at position `index` reaches the output after `index`
steps, independently of values subsequently shifted into the line. -/
theorem state_reaches_output
    {initialState finalState : Fin latency → α}
    {inputs : List α} {outputs : List α}
    (trace : Trace (Step latency) initialState inputs outputs finalState)
    (index : Fin latency) (occurs : index.val < outputs.length) :
    outputs.get ⟨index.val, occurs⟩ = initialState index := by
  cases trace with
  | nil => simp at occurs
  | cons input output step rest =>
      rename_i nextState remainingInputs remainingOutputs
      by_cases atOutput : index.val = 0
      · have positive : 0 < latency := by omega
        have indexZero : index = ⟨0, positive⟩ := by
          apply Fin.ext
          omega
        subst index
        simpa [Step, positive] using step.1
      · let previous : Fin latency := ⟨index.val - 1, by omega⟩
        have occursNormalized : index.val < remainingOutputs.length + 1 := by
          simpa using occurs
        have occursLater : previous.val < remainingOutputs.length := by
          dsimp [previous]
          omega
        have later := state_reaches_output rest previous occursLater
        have earlier : previous.val + 1 < latency := by
          dsimp [previous]
          omega
        have shifted := step.2 previous
        simp only [dif_pos earlier] at shifted
        have sameIndex :
            (⟨previous.val + 1, earlier⟩ : Fin latency) = index := by
          apply Fin.ext
          dsimp [previous]
          omega
        rw [sameIndex] at shifted
        have targetGet :
            (output :: remainingOutputs).get ⟨index.val, occurs⟩ =
              remainingOutputs.get ⟨index.val - 1, occursLater⟩ := by
          have samePosition :
              (⟨index.val, occurs⟩ : Fin (output :: remainingOutputs).length) =
                Fin.succ ⟨index.val - 1, occursLater⟩ := by
            apply Fin.ext
            simp
            omega
          rw [samePosition]
          rfl
        rw [targetGet]
        exact later.trans shifted
termination_by index.val
decreasing_by
  omega

/-- The input observed at trace position `t` is observed at the delay-line
output at position `t + latency`, whenever that later position occurs. -/
theorem input_reaches_output
    {initialState finalState : Fin latency → α}
    {inputs : List α} {outputs : List α}
    (trace : Trace (Step latency) initialState inputs outputs finalState)
    (t : Nat) (inputOccurs : t < inputs.length)
    (outputOccurs : t + latency < outputs.length) :
    outputs.get ⟨t + latency, outputOccurs⟩ =
      inputs.get ⟨t, inputOccurs⟩ := by
  induction t generalizing initialState finalState inputs outputs with
  | zero =>
      cases trace with
      | nil => simp at inputOccurs
      | cons input output step rest =>
          rename_i nextState remainingInputs remainingOutputs
          simp only [List.length_cons] at outputOccurs
          by_cases positive : 0 < latency
          · let last : Fin latency := ⟨latency - 1, by omega⟩
            have occursLater : last.val < remainingOutputs.length := by
              dsimp [last]
              omega
            have later := state_reaches_output rest last occursLater
            have shifted := step.2 last
            have noEarlier : ¬last.val + 1 < latency := by
              dsimp [last]
              omega
            simp only [dif_neg noEarlier] at shifted
            have delayed :
                remainingOutputs.get ⟨latency - 1, occursLater⟩ = input := by
              simpa [last] using later.trans shifted
            have targetGet :
                (output :: remainingOutputs).get ⟨0 + latency, by omega⟩ =
                  remainingOutputs.get ⟨latency - 1, occursLater⟩ := by
              have samePosition :
                  (⟨0 + latency, by omega⟩ :
                    Fin (output :: remainingOutputs).length) =
                    Fin.succ ⟨latency - 1, occursLater⟩ := by
                apply Fin.ext
                simp
                omega
              rw [samePosition]
              rfl
            rw [targetGet]
            exact delayed
          · have zero : latency = 0 := by omega
            subst latency
            simpa [Step] using step.1
  | succ position induction =>
      cases trace with
      | nil => simp at inputOccurs
      | cons input output step rest =>
          rename_i nextState remainingInputs remainingOutputs
          simp only [List.length_cons] at inputOccurs outputOccurs
          have inputOccursLater : position < remainingInputs.length := by omega
          have outputOccursLater : position + latency < remainingOutputs.length := by omega
          have later := induction rest inputOccursLater outputOccursLater
          have outputGet :
              (output :: remainingOutputs).get
                  ⟨position + 1 + latency, by omega⟩ =
                remainingOutputs.get
                  ⟨position + latency, outputOccursLater⟩ := by
            have samePosition :
                (⟨position + 1 + latency, by omega⟩ :
                  Fin (output :: remainingOutputs).length) =
                  Fin.succ ⟨position + latency, outputOccursLater⟩ := by
              apply Fin.ext
              simp
              omega
            rw [samePosition]
            rfl
          have inputGet :
              (input :: remainingInputs).get ⟨position + 1, by omega⟩ =
                remainingInputs.get ⟨position, inputOccursLater⟩ := by
            rfl
          rw [outputGet, inputGet]
          exact later

end Silean.DelayLine
