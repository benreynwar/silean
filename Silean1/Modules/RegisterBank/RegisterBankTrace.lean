import Silean.Contracts.Cycle.CycleTrace
import Silean.Modules.RegisterBank.RegisterBank

/-! Multi-cycle consequences of the public register-bank contract. -/

namespace Silean.Modules.RegisterBank

open Silean
open Silean.Contracts.Cycle

abbrev InputValues (element : SignalType) (addressWidth readCount : Nat) :=
  (ports element addressWidth readCount).inputs.Values

abbrev OutputValues (element : SignalType) (readCount : Nat) :=
  (outputMap element readCount).Values

def writeIndex (addressWidth : Nat)
    (input : InputValues element addressWidth readCount) :
    Fin (entryCount addressWidth) :=
  BitVector.toIndex addressWidth (input .writeAddress)

/-- Entry contents obtained by applying a finite sequence of synchronous
writes. -/
def advanceEntries (addressWidth : Nat) :
    (Fin (entryCount addressWidth) → element.Denote) →
      List (InputValues element addressWidth readCount) →
      (Fin (entryCount addressWidth) → element.Denote)
  | entries, [] => entries
  | entries, input :: rest =>
      advanceEntries addressWidth
        (nextEntries addressWidth (input .writeEnable) (input .writeAddress)
          (input .writeValue) entries) rest

@[simp] theorem advanceEntries_append (addressWidth : Nat)
    (entries : Fin (entryCount addressWidth) → element.Denote)
    (left right : List (InputValues element addressWidth readCount)) :
    advanceEntries addressWidth entries (left ++ right) =
      advanceEntries addressWidth (advanceEntries addressWidth entries left)
        right := by
  induction left generalizing entries with
  | nil => rfl
  | cons input left induction =>
      simp only [List.cons_append, advanceEntries]
      exact induction _

theorem advanceEntries_preserved (addressWidth : Nat)
    (entries : Fin (entryCount addressWidth) → element.Denote)
    (inputs : List (InputValues element addressWidth readCount))
    (index : Fin (entryCount addressWidth))
    (notWritten : ∀ input ∈ inputs,
      input .writeEnable = true → index ≠ writeIndex addressWidth input) :
    advanceEntries addressWidth entries inputs index = entries index := by
  induction inputs generalizing entries with
  | nil => rfl
  | cons input inputs induction =>
      rw [advanceEntries, induction]
      · cases enabled : input .writeEnable with
        | false => simp [nextEntries]
        | true =>
            exact nextEntries_other addressWidth true (input .writeAddress)
              (input .writeValue) entries index
              (notWritten input (by simp) enabled)
      · intro later member enabled
        exact notWritten later (by simp [member]) enabled

/-- The last enabled write to an entry determines that entry after the whole
input sequence. -/
theorem advanceEntries_of_last_write (addressWidth : Nat)
    (entries : Fin (entryCount addressWidth) → element.Denote)
    (inputs : List (InputValues element addressWidth readCount))
    (position : Nat) (occurs : position < inputs.length)
    (enabled : inputs.get ⟨position, occurs⟩ .writeEnable = true)
    (notOverwritten : ∀ later,
      (afterWrite : position < later) →
      (laterOccurs : later < inputs.length) →
      inputs.get ⟨later, laterOccurs⟩ .writeEnable = true →
      writeIndex addressWidth (inputs.get ⟨later, laterOccurs⟩) ≠
        writeIndex addressWidth (inputs.get ⟨position, occurs⟩)) :
    advanceEntries addressWidth entries inputs
        (writeIndex addressWidth (inputs.get ⟨position, occurs⟩)) =
      inputs.get ⟨position, occurs⟩ .writeValue := by
  induction position generalizing entries inputs with
  | zero =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          have headGet :
              (input :: inputs).get ⟨0, occurs⟩ = input := rfl
          rw [headGet] at enabled ⊢
          simp only [advanceEntries]
          rw [advanceEntries_preserved]
          · rw [enabled]
            exact nextEntries_selected addressWidth (input .writeAddress)
              (input .writeValue) entries
          · intro later member laterEnabled
            obtain ⟨index, equal⟩ := List.get_of_mem member
            subst later
            have different := notOverwritten (index.val + 1)
              (by omega)
              (by simpa only [List.length_cons, Nat.add_lt_add_iff_right]
                using index.isLt)
              laterEnabled
            exact Ne.symm (by simpa using different)
  | succ position induction =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          have tailOccurs : position < inputs.length := by simpa using occurs
          simp only [advanceEntries]
          apply induction _ inputs tailOccurs
          · simpa using enabled
          · intro later afterWrite laterOccurs laterEnabled
            have different := notOverwritten (later + 1)
              (by omega) (by simpa using laterOccurs) (by simpa using laterEnabled)
            simpa using different

/-- A contract trace advances the abstract entry array exactly by its input
writes. -/
theorem final_entries_of_trace
    {initial final : (stateMap element addressWidth).Values}
    {inputs : List (InputValues element addressWidth readCount)}
    {outputs : List (OutputValues element readCount)}
    (trace : Trace (cycleContract element addressWidth readCount).Transition
      initial inputs outputs final) :
    final .entries = advanceEntries addressWidth (initial .entries) inputs := by
  induction trace with
  | nil => rfl
  | @cons currentState nextState finalState remainingInputs remainingOutputs
      input output allowed rest induction =>
      rw [induction]
      change (cycleContract element addressWidth readCount).Allows
        { inputs := input
          currentState := currentState
          outputs := output
          nextState := nextState } at allowed
      have nextEqual := next_entries_of_allowed allowed
      change nextState .entries =
        nextEntries addressWidth (input .writeEnable) (input .writeAddress)
          (input .writeValue) (currentState .entries) at nextEqual
      rw [nextEqual]
      rfl

/-- After an enabled write, a later asynchronous read of the same address
returns the written value if no intervening enabled write targets that entry.
A write on the read cycle itself is deliberately permitted: the register bank
has read-old semantics within a cycle. -/
theorem read_after_write
    {initial final : (stateMap element addressWidth).Values}
    {inputs : List (InputValues element addressWidth readCount)}
    {outputs : List (OutputValues element readCount)}
    (trace : Trace (cycleContract element addressWidth readCount).Transition
      initial inputs outputs final)
    (port : Fin readCount) (writePosition readPosition : Nat)
    (writeBeforeRead : writePosition < readPosition)
    (readOccurs : readPosition < inputs.length)
    (writeEnabled :
      inputs.get ⟨writePosition, by omega⟩ .writeEnable = true)
    (sameAddress :
      BitVector.toIndex addressWidth
          (inputs.get ⟨readPosition, readOccurs⟩ (.readAddress port)) =
        writeIndex addressWidth
          (inputs.get ⟨writePosition, by omega⟩))
    (notOverwritten : ∀ position,
      (afterWrite : writePosition < position) →
      (beforeRead : position < readPosition) →
      inputs.get ⟨position, by omega⟩ .writeEnable = true →
      writeIndex addressWidth (inputs.get ⟨position, by omega⟩) ≠
        writeIndex addressWidth
          (inputs.get ⟨writePosition, by omega⟩)) :
    outputs.get ⟨readPosition, by rw [trace.length_eq]; exact readOccurs⟩
        (.readValue port) =
      inputs.get ⟨writePosition, by omega⟩ .writeValue := by
  have outputReadOccurs : readPosition < outputs.length := by
    rw [trace.length_eq]
    exact readOccurs
  have decomposed : Trace
      (cycleContract element addressWidth readCount).Transition initial
      (inputs.take readPosition ++ inputs.drop readPosition)
      (outputs.take readPosition ++ outputs.drop readPosition) final := by
    rw [List.take_append_drop, List.take_append_drop]
    exact trace
  obtain ⟨beforeRead, prefixTrace, suffixTrace⟩ := decomposed.split (by
    simp only [List.length_take]
    rw [trace.length_eq])
  have inputDrop := List.drop_eq_getElem_cons readOccurs
  have outputDrop := List.drop_eq_getElem_cons outputReadOccurs
  rw [inputDrop, outputDrop] at suffixTrace
  cases suffixTrace with
  | cons input output readAllowed rest =>
      have prefixEntries := final_entries_of_trace prefixTrace
      have writeInPrefix : writePosition < (inputs.take readPosition).length := by
        simp
        omega
      have preserved :
          beforeRead .entries
              (writeIndex addressWidth
                (inputs.get ⟨writePosition, by omega⟩)) =
            inputs.get ⟨writePosition, by omega⟩ .writeValue := by
        rw [prefixEntries]
        have writeGet :
            (inputs.take readPosition).get
                ⟨writePosition, writeInPrefix⟩ =
              inputs.get ⟨writePosition, by omega⟩ := by
          exact List.getElem_take
        have result := advanceEntries_of_last_write addressWidth
          (initial .entries) (inputs.take readPosition) writePosition
          writeInPrefix (by rw [writeGet]; exact writeEnabled)
          (by
            intro later afterWrite laterOccurs enabled
            have laterBeforeRead : later < readPosition := by
              rw [List.length_take,
                Nat.min_eq_left (Nat.le_of_lt readOccurs)] at laterOccurs
              exact laterOccurs
            have laterGet :
                (inputs.take readPosition).get ⟨later, laterOccurs⟩ =
                  inputs.get ⟨later, by omega⟩ := by
              exact List.getElem_take
            have different := notOverwritten later afterWrite laterBeforeRead
              (by rw [← laterGet]; exact enabled)
            rw [laterGet, writeGet]
            exact different)
        rw [writeGet] at result
        exact result
      have readValue := readValue_of_allowed readAllowed port
      change outputs.get ⟨readPosition, outputReadOccurs⟩ (.readValue port) =
        beforeRead .entries
          (BitVector.toIndex addressWidth
            (inputs.get ⟨readPosition, readOccurs⟩ (.readAddress port)))
        at readValue
      rw [readValue, sameAddress]
      exact preserved

end Silean.Modules.RegisterBank
