import Silean2.Contracts.NoResetFifoSerialExecution
import Silean2.Modules.Fifo
import Silean2.Modules.OneEntryFifoTemporal

namespace Silean2.Modules.Fifo.Temporal

open Silean2.Contracts

abbrev Word (signalType : SignalType) := signalType.Denote
abbrev Input (signalType : SignalType) :=
  NoResetFifo.Execution.Input (Word signalType)

def inputValues (signalType : SignalType) (input : Input signalType) :
    (OneEntryFifo.ports signalType).inputs.Values
  | .inputValid => input.enqValid
  | .inputData => input.enqData
  | .outputReady => input.deqReady

def step (behavior : Behavior signalType) (state : behavior.state.Values)
    (input : Input signalType) :
    NoResetFifo.Execution.StepResult behavior.state.Values (Word signalType) :=
  let evaluated := behavior.cycleContract.evaluate (inputValues signalType input) state
  { nextState := evaluated.2
    cycle :=
      { enqValid := input.enqValid
        enqData := input.enqData
        enqReady := evaluated.1 .inputReady
        deqValid := evaluated.1 .outputValid
        deqData := evaluated.1 .outputData
        deqReady := input.deqReady } }

def model (behavior : Behavior signalType) :
    NoResetFifo.Execution.Model behavior.state.Values (Word signalType) where
  step := step behavior

@[simp] theorem step_nextState (behavior : Behavior signalType)
    (state : behavior.state.Values) (input : Input signalType) :
    (step behavior state input).nextState =
      behavior.nextState (inputValues signalType input) state := rfl

@[simp] theorem step_enqReady (behavior : Behavior signalType)
    (state : behavior.state.Values) (input : Input signalType) :
    (step behavior state input).cycle.enqReady =
      behavior.ready input.deqReady state :=
  behavior.evaluate_ready (inputValues signalType input) state

@[simp] theorem step_deqValid (behavior : Behavior signalType)
    (state : behavior.state.Values) (input : Input signalType) :
    (step behavior state input).cycle.deqValid =
      (behavior.forward input.enqValid input.enqData state).1 :=
  (behavior.evaluate_forward (inputValues signalType input) state).1

@[simp] theorem step_deqData (behavior : Behavior signalType)
    (state : behavior.state.Values) (input : Input signalType) :
    (step behavior state input).cycle.deqData =
      (behavior.forward input.enqValid input.enqData state).2 :=
  (behavior.evaluate_forward (inputValues signalType input) state).2

def serialInputs (upstream downstream : Behavior signalType)
    (state : (upstream.serial downstream).state.Values)
    (input : Input signalType) : Input signalType × Input signalType :=
  let middleReady := downstream.ready input.deqReady (rightState state)
  let middle := upstream.forward input.enqValid input.enqData (leftState state)
  ({ enqValid := input.enqValid, enqData := input.enqData,
      deqReady := middleReady },
    { enqValid := middle.1, enqData := middle.2, deqReady := input.deqReady })

theorem serial_step_decomposes (upstream downstream : Behavior signalType)
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
        step_deqData, Behavior.serial] <;> rfl

def serialExecution (upstream downstream : Behavior signalType) :
    NoResetFifo.Execution.Serial
      (model (upstream.serial downstream)) (model upstream) (model downstream) where
  upstreamState := leftState
  downstreamState := rightState
  childInputs := serialInputs upstream downstream
  step_decomposes := serial_step_decomposes upstream downstream

structure CertifiedView (behavior : Behavior signalType) where
  view : NoResetFifo.ModuleView behavior.state.Values (Word signalType)
  satisfies : NoResetFifo.ModuleView.Satisfies view (model behavior).executes

def oneEntryView (signalType : SignalType) : CertifiedView (oneEntryBehavior signalType) where
  view := OneEntryFifo.Temporal.fifoView signalType
  satisfies := OneEntryFifo.Temporal.fifoView_satisfies signalType

@[simp] theorem oneEntryView_capacity (signalType : SignalType) :
    (oneEntryView signalType).view.capacity = 1 := rfl

@[simp] theorem oneEntryView_readyPropagationLatency (signalType : SignalType) :
    (oneEntryView signalType).view.readyPropagationLatency = 0 := rfl

def CertifiedView.serial {upstream downstream : Behavior signalType}
    (upstreamView : CertifiedView upstream) (downstreamView : CertifiedView downstream) :
    CertifiedView (upstream.serial downstream) := by
  let outerView : NoResetFifo.ModuleView
      (upstream.serial downstream).state.Values (Word signalType) :=
    { contents := fun state =>
        downstreamView.view.contents (rightState state) ++
          upstreamView.view.contents (leftState state)
      capacity := upstreamView.view.capacity + downstreamView.view.capacity
      readyPropagationLatency := upstreamView.view.readyPropagationLatency +
        downstreamView.view.readyPropagationLatency
      contents_bounded := by
        intro state
        simp only [List.length_append]
        have upstreamBound := upstreamView.view.contents_bounded (leftState state)
        have downstreamBound := downstreamView.view.contents_bounded (rightState state)
        omega }
  let constructor : NoResetFifo.ModuleView.Execution.Constructor
      outerView upstreamView.view downstreamView.view
      (model (upstream.serial downstream)) (model upstream) (model downstream) :=
    { serial := serialExecution upstream downstream
      contents := fun _ => rfl }
  exact
    { view := outerView
      satisfies := constructor.satisfies rfl rfl upstreamView.satisfies
        downstreamView.satisfies }

@[simp] theorem CertifiedView.serial_capacity
    {upstream downstream : Behavior signalType}
    (upstreamView : CertifiedView upstream) (downstreamView : CertifiedView downstream) :
    (upstreamView.serial downstreamView).view.capacity =
      upstreamView.view.capacity + downstreamView.view.capacity := rfl

@[simp] theorem CertifiedView.serial_readyPropagationLatency
    {upstream downstream : Behavior signalType}
    (upstreamView : CertifiedView upstream) (downstreamView : CertifiedView downstream) :
    (upstreamView.serial downstreamView).view.readyPropagationLatency =
      upstreamView.view.readyPropagationLatency +
        downstreamView.view.readyPropagationLatency := rfl

noncomputable def fromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) →
      CertifiedView (behaviorFromAdditional signalType additionalDepth)
  | 0 => oneEntryView signalType
  | additionalDepth + 1 =>
      (oneEntryView signalType).serial (fromAdditional signalType additionalDepth)

@[simp] theorem fromAdditional_capacity (signalType : SignalType)
    (additionalDepth : Nat) :
    (fromAdditional signalType additionalDepth).view.capacity = additionalDepth + 1 := by
  induction additionalDepth with
  | zero => rfl
  | succ additionalDepth induction =>
      simp only [fromAdditional, CertifiedView.serial_capacity,
        oneEntryView_capacity, induction]
      omega

@[simp] theorem fromAdditional_readyPropagationLatency (signalType : SignalType)
    (additionalDepth : Nat) :
    (fromAdditional signalType additionalDepth).view.readyPropagationLatency = 0 := by
  induction additionalDepth with
  | zero => rfl
  | succ additionalDepth induction =>
      simp [fromAdditional, induction]

noncomputable def certifiedView (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    CertifiedView (behavior signalType depth positive) :=
  fromAdditional signalType (additionalDepth depth)

@[simp] theorem capacity_eq_depth (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certifiedView signalType depth positive).view.capacity = depth := by
  change (fromAdditional signalType (additionalDepth depth)).view.capacity = depth
  rw [fromAdditional_capacity]
  exact additionalDepth_eq positive

@[simp] theorem readyPropagationLatency_eq_zero (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certifiedView signalType depth positive).view.readyPropagationLatency = 0 :=
  fromAdditional_readyPropagationLatency signalType (additionalDepth depth)

end Silean2.Modules.Fifo.Temporal
