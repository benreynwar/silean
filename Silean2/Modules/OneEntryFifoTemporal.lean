import Silean2.Contracts.NoResetFifoView
import Silean2.Modules.OneEntryFifo

namespace Silean2.Modules.OneEntryFifo.Temporal

open Silean2.Contracts

abbrev Word (signalType : SignalType) := signalType.Denote
abbrev ContractState (signalType : SignalType) :=
  (cycleContract signalType).state.Values
abbrev CycleInput (signalType : SignalType) :=
  NoResetFifo.Execution.Input (Word signalType)
abbrev StepResult (signalType : SignalType) :=
  NoResetFifo.Execution.StepResult (ContractState signalType) (Word signalType)

def inputValues (signalType : SignalType) (input : CycleInput signalType) :
    (ports signalType).inputs.Values := fun
  | .inputValid => input.enqValid
  | .inputData => input.enqData
  | .outputReady => input.deqReady

@[simp] theorem inputValues_inputValid (signalType : SignalType)
    (input : CycleInput signalType) :
    inputValues signalType input .inputValid = input.enqValid := rfl

@[simp] theorem inputValues_inputData (signalType : SignalType)
    (input : CycleInput signalType) :
    inputValues signalType input .inputData = input.enqData := rfl

@[simp] theorem inputValues_outputReady (signalType : SignalType)
    (input : CycleInput signalType) :
    inputValues signalType input .outputReady = input.deqReady := rfl

def step (signalType : SignalType) (state : ContractState signalType)
    (input : CycleInput signalType) : StepResult signalType :=
  let evaluated := (cycleContract signalType).evaluate
    (inputValues signalType input) state
  { nextState := evaluated.2
    cycle :=
      { enqValid := input.enqValid
        enqData := input.enqData
        enqReady := evaluated.1 .inputReady
        deqValid := evaluated.1 .outputValid
        deqData := evaluated.1 .outputData
        deqReady := input.deqReady } }

def model (signalType : SignalType) :
    NoResetFifo.Execution.Model (ContractState signalType) (Word signalType) where
  step := step signalType

@[simp] theorem step_enqValid (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).cycle.enqValid = input.enqValid := rfl

@[simp] theorem step_enqData (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).cycle.enqData = input.enqData := rfl

@[simp] theorem step_deqReady (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).cycle.deqReady = input.deqReady := rfl

def contents (state : ContractState signalType) : List (Word signalType) :=
  bif state .storedValid then [state .storedData] else []

private theorem evaluated_forward (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    let evaluated := (cycleContract signalType).evaluate
      (inputValues signalType input) state
    evaluated.1 .outputValid = (state .storedValid || input.enqValid) ∧
      evaluated.1 .outputData =
        (bif state .storedValid then state .storedData else input.enqData) := by
  intro evaluated
  have holds := ((cycleContract signalType).evaluate_evaluatesTo
    (inputValues signalType input) state).1 .forward
  have equations := (forwardRule_holds_iff signalType
    (inputValues signalType input) state evaluated.1).mp holds
  simpa using equations

private theorem evaluated_ready (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    let evaluated := (cycleContract signalType).evaluate
      (inputValues signalType input) state
    evaluated.1 .inputReady = (input.deqReady || !state .storedValid) := by
  intro evaluated
  have holds := ((cycleContract signalType).evaluate_evaluatesTo
    (inputValues signalType input) state).1 .ready
  have equation := (readyRule_holds_iff signalType
    (inputValues signalType input) state evaluated.1).mp holds
  simpa using equation

@[simp] theorem step_enqReady (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).cycle.enqReady =
      (input.deqReady || !state .storedValid) :=
  evaluated_ready signalType state input

@[simp] theorem step_deqValid (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).cycle.deqValid =
      (state .storedValid || input.enqValid) :=
  (evaluated_forward signalType state input).1

@[simp] theorem step_deqData (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).cycle.deqData =
      (bif state .storedValid then state .storedData else input.enqData) :=
  (evaluated_forward signalType state input).2

@[simp] theorem step_nextState (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).nextState =
      (cycleContract signalType).stateRule.target
        (inputValues signalType input) state := rfl

theorem contents_capacity_one (state : ContractState signalType) :
    (contents state).length ≤ 1 := by
  cases valid : state .storedValid <;> simp [contents, valid]

theorem step_conservation (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    contents state ++ (step signalType state input).cycle.acceptedInput =
      (step signalType state input).cycle.acceptedOutput ++
        contents (step signalType state input).nextState := by
  cases input with
  | mk enqValid enqData deqReady =>
      generalize validEq : state State.storedValid = storedValid
      cases storedValid <;> cases enqValid <;> cases deqReady <;>
        simp [NoResetFifo.Cycle.acceptedInput,
          NoResetFifo.Cycle.acceptedOutput, contents, step_nextState,
          cycleContract, stateRule, inputValues, validEq]

theorem run_conservation (signalType : SignalType)
    (initial : ContractState signalType)
    (inputs : List (CycleInput signalType)) :
    contents initial ++ NoResetFifo.acceptedInputs
        ((model signalType).run initial inputs).cycles =
      NoResetFifo.acceptedOutputs
          ((model signalType).run initial inputs).cycles ++
        contents ((model signalType).run initial inputs).finalState :=
  (model signalType).run_conservation contents
    (step_conservation signalType) initial inputs

theorem step_ready_stalls_bound (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    NoResetFifo.inputReadyStalls [(step signalType state input).cycle] ≤
      NoResetFifo.outputReadyStalls [(step signalType state input).cycle] := by
  cases input with
  | mk enqValid enqData deqReady =>
      cases validEq : state State.storedValid <;>
        cases deqReady <;>
        simp [NoResetFifo.inputReadyStalls, NoResetFifo.outputReadyStalls,
          validEq]

theorem ready_stalls_bound (signalType : SignalType)
    (initial : ContractState signalType)
    (inputs : List (CycleInput signalType)) :
    NoResetFifo.inputReadyStalls
        ((model signalType).run initial inputs).cycles ≤
      NoResetFifo.outputReadyStalls
        ((model signalType).run initial inputs).cycles :=
  (model signalType).run_ready_stalls_bound
    (step_ready_stalls_bound signalType) initial inputs

def trace (signalType : SignalType) (initial : ContractState signalType)
    (inputs : List (CycleInput signalType)) : NoResetFifo.Trace (Word signalType) :=
  let result := (model signalType).run initial inputs
  { initialContents := contents initial
    cycles := result.cycles
    finalContents := contents result.finalState }

theorem satisfies_contract (signalType : SignalType)
    (initial : ContractState signalType)
    (inputs : List (CycleInput signalType)) :
    NoResetFifo.Contract 1 0 (trace signalType initial inputs) := by
  constructor
  · exact run_conservation signalType initial inputs
  · intro _
    exact contents_capacity_one _
  · simpa [trace] using ready_stalls_bound signalType initial inputs

def fifoView (signalType : SignalType) :
    NoResetFifo.ModuleView (ContractState signalType) (Word signalType) where
  contents := contents
  capacity := 1
  readyPropagationLatency := 0
  contents_bounded := contents_capacity_one

def executes (signalType : SignalType) :
    NoResetFifo.ModuleView.ExecutionRelation (fifoView signalType) :=
  (model signalType).executes

theorem fifoView_satisfies (signalType : SignalType) :
    NoResetFifo.ModuleView.Satisfies (fifoView signalType)
      (executes signalType) := by
  intro initial cycles final execution
  rcases execution with ⟨inputs, cyclesEqual, finalEqual⟩
  have contract := satisfies_contract signalType initial inputs
  rw [← cyclesEqual, ← finalEqual]
  exact contract

end Silean2.Modules.OneEntryFifo.Temporal
