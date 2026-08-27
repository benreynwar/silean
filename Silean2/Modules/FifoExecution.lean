import Silean2.Contracts.NoResetFifoSerialExecution
import Silean2.Modules.FifoCycleBehavior

namespace Silean2.Modules.Fifo.Execution

open Silean2.Contracts

abbrev Word (signalType : SignalType) := signalType.Denote
abbrev Input (signalType : SignalType) :=
  NoResetFifo.Execution.Input (Word signalType)

def inputValues (signalType : SignalType) (input : Input signalType) :
    (Fifo.ports signalType).inputs.Values
  | .inputValid => input.enqValid
  | .inputData => input.enqData
  | .outputReady => input.deqReady

def step (cycleBehavior : CycleBehavior signalType)
    (state : cycleBehavior.state.Values) (input : Input signalType) :
    NoResetFifo.Execution.StepResult cycleBehavior.state.Values (Word signalType) :=
  let evaluated := cycleBehavior.cycleContract.evaluate
    (inputValues signalType input) state
  { nextState := evaluated.2
    cycle :=
      { enqValid := input.enqValid
        enqData := input.enqData
        enqReady := evaluated.1 .inputReady
        deqValid := evaluated.1 .outputValid
        deqData := evaluated.1 .outputData
        deqReady := input.deqReady } }

def model (cycleBehavior : CycleBehavior signalType) :
    NoResetFifo.Execution.Model cycleBehavior.state.Values (Word signalType) where
  step := step cycleBehavior

@[simp] theorem step_nextState (cycleBehavior : CycleBehavior signalType)
    (state : cycleBehavior.state.Values) (input : Input signalType) :
    (step cycleBehavior state input).nextState =
      cycleBehavior.nextState (inputValues signalType input) state := rfl

@[simp] theorem step_enqReady (cycleBehavior : CycleBehavior signalType)
    (state : cycleBehavior.state.Values) (input : Input signalType) :
    (step cycleBehavior state input).cycle.enqReady =
      cycleBehavior.ready input.deqReady state :=
  cycleBehavior.evaluate_ready (inputValues signalType input) state

@[simp] theorem step_deqValid (cycleBehavior : CycleBehavior signalType)
    (state : cycleBehavior.state.Values) (input : Input signalType) :
    (step cycleBehavior state input).cycle.deqValid =
      (cycleBehavior.forward input.enqValid input.enqData state).1 :=
  (cycleBehavior.evaluate_forward (inputValues signalType input) state).1

@[simp] theorem step_deqData (cycleBehavior : CycleBehavior signalType)
    (state : cycleBehavior.state.Values) (input : Input signalType) :
    (step cycleBehavior state input).cycle.deqData =
      (cycleBehavior.forward input.enqValid input.enqData state).2 :=
  (cycleBehavior.evaluate_forward (inputValues signalType input) state).2

def serialInputs (upstream downstream : CycleBehavior signalType)
    (state : (upstream.serial downstream).state.Values)
    (input : Input signalType) : Input signalType × Input signalType :=
  let middleReady := downstream.ready input.deqReady (rightState state)
  let middle := upstream.forward input.enqValid input.enqData (leftState state)
  ({ enqValid := input.enqValid, enqData := input.enqData,
      deqReady := middleReady },
    { enqValid := middle.1, enqData := middle.2, deqReady := input.deqReady })

theorem serial_step_decomposes (upstream downstream : CycleBehavior signalType)
    (state : (upstream.serial downstream).state.Values)
    (input : Input signalType) :
    NoResetFifo.Execution.StepDecomposition
      (model (upstream.serial downstream)) (model upstream) (model downstream)
      leftState rightState (serialInputs upstream downstream) state input := by
  constructor
  · rfl
  · rfl
  · constructor <;>
      simp only [model, serialInputs, step_enqReady, step_deqValid,
        step_deqData, CycleBehavior.serial] <;> rfl

def serial (upstream downstream : CycleBehavior signalType) :
    NoResetFifo.Execution.Serial
      (model (upstream.serial downstream)) (model upstream) (model downstream) where
  upstreamState := leftState
  downstreamState := rightState
  childInputs := serialInputs upstream downstream
  step_decomposes := serial_step_decomposes upstream downstream

end Silean2.Modules.Fifo.Execution
