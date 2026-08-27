import Silean2.Contracts.NoResetFifoView
import Silean2.Modules.FifoExecution
import Silean2.Modules.OneEntryFifo

namespace Silean2.Modules.OneEntryFifo.Properties

open Silean2.Contracts

abbrev Word (signalType : SignalType) := signalType.Denote
abbrev ContractState (signalType : SignalType) :=
  (cycleContract signalType).state.Values
abbrev CycleInput (signalType : SignalType) :=
  Fifo.Execution.Input signalType
abbrev StepResult (signalType : SignalType) :=
  NoResetFifo.Execution.StepResult (ContractState signalType) (Word signalType)

def inputValues (signalType : SignalType) (input : CycleInput signalType) :
    (Fifo.ports signalType).inputs.Values :=
  Fifo.Execution.inputValues signalType input

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
  Fifo.Execution.step (Fifo.oneEntryCycleBehavior signalType) state input

def model (signalType : SignalType) :
    NoResetFifo.Execution.Model (ContractState signalType) (Word signalType) :=
  Fifo.Execution.model (Fifo.oneEntryCycleBehavior signalType)

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

@[simp] theorem step_enqReady (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).cycle.enqReady =
      (input.deqReady || !state .storedValid) :=
  Fifo.Execution.step_enqReady (Fifo.oneEntryCycleBehavior signalType) state input

@[simp] theorem step_deqValid (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).cycle.deqValid =
      (state .storedValid || input.enqValid) :=
  Fifo.Execution.step_deqValid (Fifo.oneEntryCycleBehavior signalType) state input

@[simp] theorem step_deqData (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).cycle.deqData =
      (bif state .storedValid then state .storedData else input.enqData) :=
  Fifo.Execution.step_deqData (Fifo.oneEntryCycleBehavior signalType) state input

@[simp] theorem step_nextState (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).nextState =
      (cycleContract signalType).stateRule.apply
        (inputValues signalType input) state := by
  exact Fifo.Execution.step_nextState
    (Fifo.oneEntryCycleBehavior signalType) state input

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
          cycleContract, stateRule, inputValues, validEq,
          Fifo.Execution.inputValues,
          CycleStateRule.apply, SignalSelection.project,
          SignalSelection.prepend, SignalMap.select]

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
    NoResetFifo.View (ContractState signalType) (Word signalType) where
  contents := contents
  capacity := 1
  readyPropagationLatency := 0
  contents_bounded := contents_capacity_one

def executes (signalType : SignalType) :
    NoResetFifo.View.ExecutionRelation (fifoView signalType) :=
  (model signalType).executes

theorem fifoView_satisfies (signalType : SignalType) :
    NoResetFifo.View.Satisfies (fifoView signalType)
      (executes signalType) := by
  intro initial cycles final execution
  rcases execution with ⟨inputs, cyclesEqual, finalEqual⟩
  have contract := satisfies_contract signalType initial inputs
  rw [← cyclesEqual, ← finalEqual]
  exact contract

end Silean2.Modules.OneEntryFifo.Properties
