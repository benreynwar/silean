import Silean.ModuleResetContract
import Silean.Modules.FifoInterface

namespace Silean.Modules.Fifo.Reset

open Silean

abbrev Word (element : SignalType) := element.Denote

def capacity (addressWidth : Nat) : Nat := 2 ^ addressWidth

def outputValid (queue : List α) : Bool := !queue.isEmpty

def inputReady (addressWidth : Nat) (queue : List α) : Bool :=
  decide (queue.length < capacity addressWidth)

def acceptsInput (addressWidth : Nat) (inputValid : Bool)
    (queue : List α) : Bool :=
  inputValid && inputReady addressWidth queue

def acceptsOutput (outputReady : Bool) (queue : List α) : Bool :=
  outputReady && outputValid queue

def nextQueue (addressWidth : Nat) (inputValid : Bool) (inputData : α)
    (outputReady : Bool) (queue : List α) : List α :=
  let remaining := if acceptsOutput outputReady queue then queue.drop 1 else queue
  if acceptsInput addressWidth inputValid queue then remaining ++ [inputData]
  else remaining

def outputExpectations (element : SignalType) (addressWidth : Nat)
    (queue : List (Word element)) : (Fifo.ports element).outputs.Expectations
  | .outputValid => .exact (outputValid queue)
  | .outputData => match queue with
    | [] => element.dontCareExpectation
    | head :: _ => element.exactExpectation head
  | .inputReady => .exact (inputReady addressWidth queue)

def contract (element : SignalType) (addressWidth : Nat) :
    ModuleResetContract (Fifo.ports element) where
  State := List (Word element)
  resetInput := .reset
  resetInputType := rfl
  resetState := []
  step inputs queue :=
    (outputExpectations element addressWidth queue,
      nextQueue addressWidth (inputs .inputValid) (inputs .inputData)
        (inputs .outputReady) queue)

def SynchronizationBounded (addressWidth : Nat) : Option (List α) → Prop
  | none => True
  | some queue => queue.length ≤ capacity addressWidth

@[simp] theorem capacity_positive (addressWidth : Nat) :
    0 < capacity addressWidth := by
  exact Nat.two_pow_pos addressWidth

@[simp] theorem reset_state (element : SignalType) (addressWidth : Nat) :
    (contract element addressWidth).resetState = [] := rfl

@[simp] theorem reset_asserted
    (inputs : (Fifo.ports element).inputs.Values) :
    (contract element addressWidth).resetAsserted inputs = inputs .reset := rfl

@[simp] theorem contract_step_expectations (element : SignalType)
    (addressWidth : Nat) (inputs : (Fifo.ports element).inputs.Values)
    (queue : List (Word element)) :
    ((contract element addressWidth).step inputs queue).1 =
      outputExpectations element addressWidth queue := rfl

@[simp] theorem contract_step_state (element : SignalType)
    (addressWidth : Nat) (inputs : (Fifo.ports element).inputs.Values)
    (queue : List (Word element)) :
    ((contract element addressWidth).step inputs queue).2 =
      nextQueue addressWidth (inputs .inputValid) (inputs .inputData)
        (inputs .outputReady) queue := rfl

@[simp] theorem outputValid_nil : outputValid ([] : List α) = false := rfl

@[simp] theorem outputValid_cons (head : α) (tail : List α) :
    outputValid (head :: tail) = true := rfl

@[simp] theorem inputReady_nil (addressWidth : Nat) :
    inputReady addressWidth ([] : List α) = true := by
  simp [inputReady]

@[simp] theorem inputReady_eq_true_iff (addressWidth : Nat) (queue : List α) :
    inputReady addressWidth queue = true ↔ queue.length < capacity addressWidth := by
  simp [inputReady]

@[simp] theorem inputReady_eq_false_iff (addressWidth : Nat) (queue : List α) :
    inputReady addressWidth queue = false ↔ capacity addressWidth ≤ queue.length := by
  simp [inputReady]

@[simp] theorem outputValid_eq_true_iff (queue : List α) :
    outputValid queue = true ↔ queue ≠ [] := by
  cases queue <;> simp

@[simp] theorem outputValid_eq_false_iff (queue : List α) :
    outputValid queue = false ↔ queue = [] := by
  cases queue <;> simp

@[simp] theorem outputExpectations_empty_valid (element : SignalType)
    (addressWidth : Nat) :
    outputExpectations element addressWidth [] .outputValid = .zero := rfl

@[simp] theorem outputExpectations_empty_data (element : SignalType)
    (addressWidth : Nat) :
    outputExpectations element addressWidth [] .outputData =
      element.dontCareExpectation := rfl

@[simp] theorem outputExpectations_empty_ready (element : SignalType)
    (addressWidth : Nat) :
    outputExpectations element addressWidth [] .inputReady = .one := by
  simp [outputExpectations, BitExpectation.exact]

@[simp] theorem outputExpectations_cons_valid (element : SignalType)
    (addressWidth : Nat) (head : Word element) (tail : List (Word element)) :
    outputExpectations element addressWidth (head :: tail) .outputValid = .one := by
  simp [outputExpectations, outputValid, BitExpectation.exact]

@[simp] theorem outputExpectations_cons_data (element : SignalType)
    (addressWidth : Nat) (head : Word element) (tail : List (Word element)) :
    outputExpectations element addressWidth (head :: tail) .outputData =
      element.exactExpectation head := rfl

theorem nextQueue_stall (addressWidth : Nat) (inputValid : Bool)
    (inputData : α) (outputReady : Bool) (queue : List α)
    (noInput : acceptsInput addressWidth inputValid queue = false)
    (noOutput : acceptsOutput outputReady queue = false) :
    nextQueue addressWidth inputValid inputData outputReady queue = queue := by
  simp [nextQueue, noInput, noOutput]

theorem nextQueue_enqueue (addressWidth : Nat) (inputValid : Bool)
    (inputData : α) (outputReady : Bool) (queue : List α)
    (inputAccepted : acceptsInput addressWidth inputValid queue = true)
    (noOutput : acceptsOutput outputReady queue = false) :
    nextQueue addressWidth inputValid inputData outputReady queue =
      queue ++ [inputData] := by
  simp [nextQueue, inputAccepted, noOutput]

theorem nextQueue_dequeue (addressWidth : Nat) (inputValid : Bool)
    (inputData : α) (outputReady : Bool) (queue : List α)
    (noInput : acceptsInput addressWidth inputValid queue = false)
    (outputAccepted : acceptsOutput outputReady queue = true) :
    nextQueue addressWidth inputValid inputData outputReady queue = queue.drop 1 := by
  simp [nextQueue, noInput, outputAccepted]

theorem nextQueue_simultaneous (addressWidth : Nat) (inputValid : Bool)
    (inputData : α) (outputReady : Bool) (queue : List α)
    (inputAccepted : acceptsInput addressWidth inputValid queue = true)
    (outputAccepted : acceptsOutput outputReady queue = true) :
    nextQueue addressWidth inputValid inputData outputReady queue =
      queue.drop 1 ++ [inputData] := by
  simp [nextQueue, inputAccepted, outputAccepted]

theorem nextQueue_capacity (addressWidth : Nat) (inputValid : Bool)
    (inputData : α) (outputReady : Bool) (queue : List α)
    (bounded : queue.length ≤ capacity addressWidth) :
    (nextQueue addressWidth inputValid inputData outputReady queue).length ≤
      capacity addressWidth := by
  by_cases inputAccepted : acceptsInput addressWidth inputValid queue = true
  · have below : queue.length < capacity addressWidth := by
      have accepted := inputAccepted
      simp [acceptsInput] at accepted
      exact accepted.2
    by_cases outputAccepted : acceptsOutput outputReady queue = true
    · rw [nextQueue_simultaneous addressWidth inputValid inputData outputReady
        queue inputAccepted outputAccepted]
      simp only [List.length_append, List.length_drop, List.length_singleton]
      omega
    · have outputRejected : acceptsOutput outputReady queue = false := by
        cases equal : acceptsOutput outputReady queue <;> simp_all
      rw [nextQueue_enqueue addressWidth inputValid inputData outputReady queue
        inputAccepted outputRejected]
      simp
      omega
  · have inputRejected : acceptsInput addressWidth inputValid queue = false := by
      cases equal : acceptsInput addressWidth inputValid queue <;> simp_all
    by_cases outputAccepted : acceptsOutput outputReady queue = true
    · rw [nextQueue_dequeue addressWidth inputValid inputData outputReady queue
        inputRejected outputAccepted]
      simp only [List.length_drop]
      omega
    · have outputRejected : acceptsOutput outputReady queue = false := by
        cases equal : acceptsOutput outputReady queue <;> simp_all
      rw [nextQueue_stall addressWidth inputValid inputData outputReady queue
        inputRejected outputRejected]
      exact bounded

theorem TraceMatches.preserves_capacity (element : SignalType)
    (addressWidth : Nat)
    {initial final : (contract element addressWidth).Synchronization}
    {inputs : List (Fifo.ports element).inputs.Values}
    {outputs : List (Fifo.ports element).outputs.Values}
    (trace : (contract element addressWidth).TraceMatches
      initial inputs outputs final)
    (initialBounded : SynchronizationBounded addressWidth initial) :
    SynchronizationBounded addressWidth final := by
  induction trace with
  | nil => exact initialBounded
  | cons input output cycle rest induction =>
      apply induction
      cases cycle with
      | reset => simp [SynchronizationBounded]
      | beforeReset => trivial
      | ordinary =>
          exact nextQueue_capacity addressWidth (input .inputValid)
            (input .inputData) (input .outputReady) _ initialBounded

@[simp] theorem trace_cons_reset_iff (element : SignalType) (addressWidth : Nat)
    {initial final : (contract element addressWidth).Synchronization}
    {resetInput : (Fifo.ports element).inputs.Values}
    {inputs : List (Fifo.ports element).inputs.Values}
    {resetOutput : (Fifo.ports element).outputs.Values}
    {outputs : List (Fifo.ports element).outputs.Values}
    (asserted : resetInput .reset = true) :
    (contract element addressWidth).TraceMatches initial
        (resetInput :: inputs) (resetOutput :: outputs) final ↔
      (contract element addressWidth).TraceMatches (some [])
        inputs outputs final :=
  ModuleResetContract.TraceMatches.cons_reset_iff asserted

theorem trace_suffix_after_reset (element : SignalType) (addressWidth : Nat)
    {initial final : (contract element addressWidth).Synchronization}
    {prefixInputs : List (Fifo.ports element).inputs.Values}
    {resetInput : (Fifo.ports element).inputs.Values}
    {inputs : List (Fifo.ports element).inputs.Values}
    {prefixOutputs : List (Fifo.ports element).outputs.Values}
    {resetOutput : (Fifo.ports element).outputs.Values}
    {outputs : List (Fifo.ports element).outputs.Values}
    (prefixLengths : prefixOutputs.length = prefixInputs.length)
    (asserted : resetInput .reset = true)
    (trace : (contract element addressWidth).TraceMatches initial
      (prefixInputs ++ resetInput :: inputs)
      (prefixOutputs ++ resetOutput :: outputs) final) :
    (contract element addressWidth).TraceMatches (some [])
      inputs outputs final := by
  rcases ModuleResetContract.TraceMatches.split trace prefixLengths with
    ⟨_, _, suffix⟩
  exact (trace_cons_reset_iff element addressWidth asserted).mp suffix

theorem TraceMatches.bounded_after_reset (element : SignalType)
    (addressWidth : Nat)
    {initial final : (contract element addressWidth).Synchronization}
    {resetInput : (Fifo.ports element).inputs.Values}
    {inputs : List (Fifo.ports element).inputs.Values}
    {resetOutput : (Fifo.ports element).outputs.Values}
    {outputs : List (Fifo.ports element).outputs.Values}
    (asserted : resetInput .reset = true)
    (trace : (contract element addressWidth).TraceMatches initial
      (resetInput :: inputs) (resetOutput :: outputs) final) :
    SynchronizationBounded addressWidth final := by
  have tail := (trace_cons_reset_iff element addressWidth asserted).mp trace
  exact TraceMatches.preserves_capacity element addressWidth tail (by
    simp [SynchronizationBounded])

end Silean.Modules.Fifo.Reset

namespace Silean.Modules.Fifo

/-! The public FIFO reset contract; queue mechanics and laws live under
`Fifo.Reset`. -/
abbrev resetContract := Reset.contract

end Silean.Modules.Fifo
