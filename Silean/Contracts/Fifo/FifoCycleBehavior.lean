import Silean.Contracts.Cycle.CycleImplementation
import Silean.Interfaces.FifoPorts

namespace Silean.Contracts.Fifo.Cycle

open Silean

/-! A convenient exact-cycle description for valid/ready FIFO modules. It
separates forward valid/data behavior, backward ready behavior, and the state
transition, then packages them as a normal cycle contract. -/

inductive Rule
  | forward
  | ready
deriving Enumeration

def sumState (left right : SignalMap) : SignalMap where
  Key := Sum left.Key right.Key
  keys := Enumeration.sum left.keys right.keys
  value
    | .inl key => left.value key
    | .inr key => right.value key

def leftState (values : (sumState left right).Values) : left.Values :=
  fun key => values (.inl key)

def rightState (values : (sumState left right).Values) : right.Values :=
  fun key => values (.inr key)

def combineState (leftValues : left.Values) (rightValues : right.Values) :
    (sumState left right).Values
  | .inl key => leftValues key
  | .inr key => rightValues key

structure CycleBehavior (signalType : SignalType) where
  /-- Lean state used by this exact FIFO behavior. -/
  state : SignalMap
  /-- Computes output valid and data from incoming valid/data and current state. -/
  forward : Bool → signalType.Denote → state.Values →
    Bool × signalType.Denote
  /-- Computes input readiness from output readiness and current state. -/
  ready : Bool → state.Values → Bool
  /-- Computes complete next state from the FIFO boundary and current state. -/
  nextState : (Silean.Interfaces.Fifo.ports signalType).inputs.Values →
    state.Values → state.Values

namespace CycleBehavior

def forwardRule (behavior : CycleBehavior signalType) :
    Contracts.Cycle.CycleOutputRule (Silean.Interfaces.Fifo.ports signalType) behavior.state
      (.ofLists [.bit, signalType] [.bit, signalType]) where
  readsInputs := ((Silean.Interfaces.Fifo.inputMap signalType).select .inputData).prepend
    .inputValid
  writesOutputs := ((Silean.Interfaces.Fifo.outputMap signalType).select .outputData).prepend
    .outputValid
  target
    | (inputValid, (inputData, ())), state =>
        let result := behavior.forward inputValid inputData state
        (result.1, (result.2, ()))

def readyRule (behavior : CycleBehavior signalType) :
    Contracts.Cycle.CycleOutputRule (Silean.Interfaces.Fifo.ports signalType) behavior.state
      (.ofLists [.bit] [.bit]) where
  readsInputs := (Silean.Interfaces.Fifo.inputMap signalType).select .outputReady
  writesOutputs := (Silean.Interfaces.Fifo.outputMap signalType).select .inputReady
  target
    | (outputReady, ()), state => (behavior.ready outputReady state, ())

def stateRule (behavior : CycleBehavior signalType) :
    Contracts.Cycle.CycleStateRule (Silean.Interfaces.Fifo.ports signalType) behavior.state where
  inputTypes := .cons .bit (.cons .bit (.cons .bit (.cons signalType .nil)))
  readsInputs :=
    ((((Silean.Interfaces.Fifo.inputMap signalType).select .inputData).prepend .inputValid).prepend
      .outputReady).prepend .reset
  target
    | (reset, (outputReady, (inputValid, (inputData, ())))), state =>
        behavior.nextState (fun
          | .inputValid => inputValid
          | .inputData => inputData
          | .outputReady => outputReady
          | .reset => reset) state

def cycleContract (behavior : CycleBehavior signalType) :
    Contracts.Cycle.ModuleCycleContract (Silean.Interfaces.Fifo.ports signalType) where
  state := behavior.state
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => ⟨_, behavior.forwardRule⟩
    | .ready => ⟨_, behavior.readyRule⟩
  stateRule := behavior.stateRule
  outputCoverage := by rfl

@[simp] theorem stateRule_apply (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    behavior.stateRule.apply inputs state = behavior.nextState inputs state := by
  simp only [stateRule, Contracts.Cycle.CycleStateRule.apply, SignalSelection.project,
    SignalSelection.prepend, SignalMap.select]
  congr 1
  funext input
  cases input <;> rfl

@[simp] theorem cycleContract_stateRule_apply (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    behavior.cycleContract.stateRule.apply inputs state =
      behavior.nextState inputs state :=
  behavior.stateRule_apply inputs state

@[simp] theorem cycleContract_forward_reads (behavior : CycleBehavior signalType) :
    ((behavior.cycleContract.outputRule Rule.forward).2.readsInputs.labels) =
      [.inputValid, .inputData] := rfl

@[simp] theorem cycleContract_forward_writes (behavior : CycleBehavior signalType) :
    ((behavior.cycleContract.outputRule Rule.forward).2.writesOutputs.labels) =
      [.outputValid, .outputData] := rfl

@[simp] theorem cycleContract_ready_reads (behavior : CycleBehavior signalType) :
    ((behavior.cycleContract.outputRule Rule.ready).2.readsInputs.labels) =
      [.outputReady] := rfl

@[simp] theorem cycleContract_ready_writes (behavior : CycleBehavior signalType) :
    ((behavior.cycleContract.outputRule Rule.ready).2.writesOutputs.labels) =
      [.inputReady] := rfl

theorem forwardRule_holds_iff (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values)
    (outputs : (Silean.Interfaces.Fifo.ports signalType).outputs.Values) :
    behavior.forwardRule.Holds inputs state outputs ↔
      outputs .outputValid =
          (behavior.forward (inputs .inputValid) (inputs .inputData) state).1 ∧
      outputs .outputData =
          (behavior.forward (inputs .inputValid) (inputs .inputData) state).2 := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, forwardRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]

theorem readyRule_holds_iff (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values)
    (outputs : (Silean.Interfaces.Fifo.ports signalType).outputs.Values) :
    behavior.readyRule.Holds inputs state outputs ↔
      outputs .inputReady = behavior.ready (inputs .outputReady) state := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, readyRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

theorem evaluate_forward (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    let evaluated := behavior.cycleContract.evaluate inputs state
    evaluated.1 .outputValid =
        (behavior.forward (inputs .inputValid) (inputs .inputData) state).1 ∧
      evaluated.1 .outputData =
        (behavior.forward (inputs .inputValid) (inputs .inputData) state).2 := by
  intro evaluated
  have holds : behavior.forwardRule.Holds inputs state evaluated.1 :=
    (behavior.cycleContract.evaluate_evaluatesTo inputs state).1 .forward
  exact (behavior.forwardRule_holds_iff inputs state evaluated.1).mp
    holds

theorem evaluate_ready (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    let evaluated := behavior.cycleContract.evaluate inputs state
    evaluated.1 .inputReady = behavior.ready (inputs .outputReady) state := by
  intro evaluated
  have holds : behavior.readyRule.Holds inputs state evaluated.1 :=
    (behavior.cycleContract.evaluate_evaluatesTo inputs state).1 .ready
  exact (behavior.readyRule_holds_iff inputs state evaluated.1).mp
    holds

@[simp] theorem evaluate_outputValid (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    (behavior.cycleContract.evaluate inputs state).1 .outputValid =
      (behavior.forward (inputs .inputValid) (inputs .inputData) state).1 :=
  (behavior.evaluate_forward inputs state).1

@[simp] theorem evaluate_outputData (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    (behavior.cycleContract.evaluate inputs state).1 .outputData =
      (behavior.forward (inputs .inputValid) (inputs .inputData) state).2 :=
  (behavior.evaluate_forward inputs state).2

@[simp] theorem evaluate_inputReady (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    (behavior.cycleContract.evaluate inputs state).1 .inputReady =
      behavior.ready (inputs .outputReady) state :=
  behavior.evaluate_ready inputs state

@[simp] theorem evaluate_nextState (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    (behavior.cycleContract.evaluate inputs state).2 =
      behavior.nextState inputs state :=
  behavior.cycleContract_stateRule_apply inputs state

def serial (upstream downstream : CycleBehavior signalType) : CycleBehavior signalType where
  state := sumState upstream.state downstream.state
  forward := fun inputValid inputData state =>
    let middle := upstream.forward inputValid inputData (leftState state)
    downstream.forward middle.1 middle.2 (rightState state)
  ready := fun outputReady state =>
    let middleReady := downstream.ready outputReady (rightState state)
    upstream.ready middleReady (leftState state)
  nextState := fun inputs state =>
    let upstreamState := leftState state
    let downstreamState := rightState state
    let middle := upstream.forward (inputs .inputValid) (inputs .inputData)
      upstreamState
    let middleReady := downstream.ready (inputs .outputReady) downstreamState
    let upstreamInputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values := fun
      | .inputValid => inputs .inputValid
      | .inputData => inputs .inputData
      | .outputReady => middleReady
      | .reset => inputs .reset
    let downstreamInputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values := fun
      | .inputValid => middle.1
      | .inputData => middle.2
      | .outputReady => inputs .outputReady
      | .reset => inputs .reset
    combineState (upstream.nextState upstreamInputs upstreamState)
      (downstream.nextState downstreamInputs downstreamState)

end CycleBehavior

structure CertifiedCycleBehavior (signalType : SignalType) where
  cycleBehavior : CycleBehavior signalType
  moduleStructure : ModuleStructure (Silean.Interfaces.Fifo.ports signalType)
  certification : Contracts.Cycle.ModuleCycleCertification moduleStructure cycleBehavior.cycleContract

def CertifiedCycleBehavior.certified (value : CertifiedCycleBehavior signalType) :
    Contracts.Cycle.ModuleCycleCertified (Silean.Interfaces.Fifo.ports signalType) :=
  value.certification.bundle

@[simp] theorem CertifiedCycleBehavior.certified_cycleContract
    (value : CertifiedCycleBehavior signalType) :
    value.certified.cycleContract = value.cycleBehavior.cycleContract := rfl

@[simp] theorem CertifiedCycleBehavior.certified_stateRule_apply
    (value : CertifiedCycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : value.certified.cycleContract.state.Values) :
    value.certified.cycleContract.stateRule.apply inputs state =
      value.cycleBehavior.nextState inputs state := by
  change value.cycleBehavior.cycleContract.stateRule.apply inputs state = _
  exact value.cycleBehavior.cycleContract_stateRule_apply inputs state

end Silean.Contracts.Fifo.Cycle
