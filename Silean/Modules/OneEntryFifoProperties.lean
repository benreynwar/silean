import Silean.Contracts.NoResetFifoView
import Silean.Modules.NoResetFifoExecution
import Silean.Modules.OneEntryFifo

namespace Silean.Modules.OneEntryFifo.Properties

open Silean.Contracts

abbrev Word (signalType : SignalType) := signalType.Denote
abbrev ContractState (signalType : SignalType) :=
  (cycleContract signalType).state.Values
abbrev CycleInput (signalType : SignalType) :=
  NoResetFifo.Execution.Input signalType
abbrev StepResult (signalType : SignalType) :=
  NoResetFifo.Execution.StepResult (ContractState signalType) (Word signalType)

def inputValues (signalType : SignalType) (input : CycleInput signalType) :
    (NoResetFifo.ports signalType).inputs.Values :=
  NoResetFifo.Execution.inputValues signalType input

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
  NoResetFifo.Execution.step (NoResetFifo.oneEntryCycleBehavior signalType) state input

def model (signalType : SignalType) :
    NoResetFifo.Execution.Model (ContractState signalType) (Word signalType) :=
  NoResetFifo.Execution.model (NoResetFifo.oneEntryCycleBehavior signalType)

@[simp] theorem step_enqValid (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).observation.enqValid = input.enqValid := rfl

@[simp] theorem step_enqData (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).observation.enqData = input.enqData := rfl

@[simp] theorem step_deqReady (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).observation.deqReady = input.deqReady := rfl

def contents (state : ContractState signalType) : List (Word signalType) :=
  bif state .storedValid then [state .storedData] else []

@[simp] theorem step_enqReady (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).observation.enqReady =
      (input.deqReady || !state .storedValid) :=
  NoResetFifo.Execution.step_enqReady (NoResetFifo.oneEntryCycleBehavior signalType) state input

@[simp] theorem step_deqValid (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).observation.deqValid =
      (state .storedValid || input.enqValid) :=
  NoResetFifo.Execution.step_deqValid (NoResetFifo.oneEntryCycleBehavior signalType) state input

@[simp] theorem step_deqData (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).observation.deqData =
      (bif state .storedValid then state .storedData else input.enqData) :=
  NoResetFifo.Execution.step_deqData (NoResetFifo.oneEntryCycleBehavior signalType) state input

@[simp] theorem step_nextState (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    (step signalType state input).nextState =
      (cycleContract signalType).stateRule.apply
        (inputValues signalType input) state := by
  exact NoResetFifo.Execution.step_nextState
    (NoResetFifo.oneEntryCycleBehavior signalType) state input

theorem contents_capacity_one (state : ContractState signalType) :
    (contents state).length ≤ 1 := by
  cases valid : state .storedValid <;> simp [contents, valid]

theorem step_conservation (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    contents state ++ (step signalType state input).observation.acceptedInput =
      (step signalType state input).observation.acceptedOutput ++
        contents (step signalType state input).nextState := by
  cases input with
  | mk enqValid enqData deqReady =>
      generalize validEq : state State.storedValid = storedValid
      cases storedValid <;> cases enqValid <;> cases deqReady <;>
        simp [NoResetFifo.Cycle.acceptedInput,
          NoResetFifo.Cycle.acceptedOutput, contents, step_nextState,
          cycleContract, stateRule, inputValues, validEq,
          NoResetFifo.Execution.inputValues,
          CycleStateRule.apply, SignalSelection.project,
          SignalSelection.prepend, SignalMap.select]

theorem run_conservation (signalType : SignalType)
    (initial : ContractState signalType)
    (inputs : List (CycleInput signalType)) :
    contents initial ++ NoResetFifo.acceptedInputs
        ((model signalType).run initial inputs).observations =
      NoResetFifo.acceptedOutputs
          ((model signalType).run initial inputs).observations ++
        contents ((model signalType).run initial inputs).finalState :=
  (model signalType).run_conservation contents
    (step_conservation signalType) initial inputs

theorem step_ready_stalls_bound (signalType : SignalType)
    (state : ContractState signalType) (input : CycleInput signalType) :
    NoResetFifo.inputReadyStalls [(step signalType state input).observation] ≤
      NoResetFifo.outputReadyStalls [(step signalType state input).observation] := by
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
        ((model signalType).run initial inputs).observations ≤
      NoResetFifo.outputReadyStalls
        ((model signalType).run initial inputs).observations :=
  (model signalType).run_ready_stalls_bound
    (step_ready_stalls_bound signalType) initial inputs

def trace (signalType : SignalType) (initial : ContractState signalType)
    (inputs : List (CycleInput signalType)) : NoResetFifo.Trace (Word signalType) :=
  let result := (model signalType).run initial inputs
  { initialContents := contents initial
    cycles := result.observations
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

end Silean.Modules.OneEntryFifo.Properties
