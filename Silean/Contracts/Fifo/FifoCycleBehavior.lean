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

namespace ForwardRule
inductive Input | inputValid | inputData deriving Enumeration
inductive Output | outputValid | outputData deriving Enumeration
end ForwardRule

namespace ReadyRule
inductive Input | outputReady deriving Enumeration
inductive Output | inputReady deriving Enumeration
end ReadyRule

@[reducible] def forwardInputGroup (signalType : SignalType) :
    SignalGroup (Silean.Interfaces.Fifo.inputMap signalType) :=
  SignalGroup.fromLabels (Silean.Interfaces.Fifo.inputMap signalType)
    ForwardRule.Input fun
      | .inputValid => .inputValid
      | .inputData => .inputData

@[reducible] def forwardOutputGroup (signalType : SignalType) :
    SignalGroup (Silean.Interfaces.Fifo.outputMap signalType) :=
  SignalGroup.fromLabels (Silean.Interfaces.Fifo.outputMap signalType)
    ForwardRule.Output fun
      | .outputValid => .outputValid
      | .outputData => .outputData

@[reducible] def readyInputGroup (signalType : SignalType) :
    SignalGroup (Silean.Interfaces.Fifo.inputMap signalType) :=
  SignalGroup.fromLabels (Silean.Interfaces.Fifo.inputMap signalType)
    ReadyRule.Input fun | .outputReady => .outputReady

@[reducible] def readyOutputGroup (signalType : SignalType) :
    SignalGroup (Silean.Interfaces.Fifo.outputMap signalType) :=
  SignalGroup.fromLabels (Silean.Interfaces.Fifo.outputMap signalType)
    ReadyRule.Output fun | .inputReady => .inputReady

def forwardRule (behavior : CycleBehavior signalType) :
    Contracts.Cycle.CycleOutputRule
      (Silean.Interfaces.Fifo.ports signalType) behavior.state where
  readsInputs := forwardInputGroup signalType
  writesOutputs := forwardOutputGroup signalType
  target inputs state := fun
    | .outputValid =>
        (behavior.forward (inputs .inputValid) (inputs .inputData) state).1
    | .outputData =>
        (behavior.forward (inputs .inputValid) (inputs .inputData) state).2

def readyRule (behavior : CycleBehavior signalType) :
    Contracts.Cycle.CycleOutputRule
      (Silean.Interfaces.Fifo.ports signalType) behavior.state where
  readsInputs := readyInputGroup signalType
  writesOutputs := readyOutputGroup signalType
  target inputs state := fun
    | .inputReady => behavior.ready (inputs .outputReady) state

def stateRule (behavior : CycleBehavior signalType) :
    Contracts.Cycle.CycleStateRule (Silean.Interfaces.Fifo.ports signalType) behavior.state where
  readsInputs := .all (Silean.Interfaces.Fifo.ports signalType).inputs
  target := behavior.nextState

def cycleContract (behavior : CycleBehavior signalType) :
    Contracts.Cycle.ModuleCycleContract (Silean.Interfaces.Fifo.ports signalType) where
  state := behavior.state
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => behavior.forwardRule
    | .ready => behavior.readyRule
  stateRule := behavior.stateRule
  outputCoverage := by rfl

@[simp] theorem stateRule_apply (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    behavior.stateRule.apply inputs state = behavior.nextState inputs state := by
  simp [stateRule, Contracts.Cycle.CycleStateRule.apply]

@[simp] theorem cycleContract_stateRule_apply (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    behavior.cycleContract.stateRule.apply inputs state =
      behavior.nextState inputs state :=
  behavior.stateRule_apply inputs state

@[simp] theorem cycleContract_forward_reads (behavior : CycleBehavior signalType) :
    ((behavior.cycleContract.outputRule Rule.forward).readsInputs.labels) =
      [.inputValid, .inputData] := rfl

@[simp] theorem cycleContract_forward_writes (behavior : CycleBehavior signalType) :
    ((behavior.cycleContract.outputRule Rule.forward).writesOutputs.labels) =
      [.outputValid, .outputData] := rfl

@[simp] theorem cycleContract_ready_reads (behavior : CycleBehavior signalType) :
    ((behavior.cycleContract.outputRule Rule.ready).readsInputs.labels) =
      [.outputReady] := rfl

@[simp] theorem cycleContract_ready_writes (behavior : CycleBehavior signalType) :
    ((behavior.cycleContract.outputRule Rule.ready).writesOutputs.labels) =
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
  unfold forwardRule Contracts.Cycle.CycleOutputRule.Holds SignalGroup.Matches
  constructor
  · intro equal
    exact ⟨congrFun equal .outputValid, congrFun equal .outputData⟩
  · rintro ⟨valid, data⟩
    funext output
    cases output <;> assumption

theorem readyRule_holds_iff (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values)
    (outputs : (Silean.Interfaces.Fifo.ports signalType).outputs.Values) :
    behavior.readyRule.Holds inputs state outputs ↔
      outputs .inputReady = behavior.ready (inputs .outputReady) state := by
  unfold readyRule Contracts.Cycle.CycleOutputRule.Holds SignalGroup.Matches
  constructor
  · intro equal
    exact congrFun equal .inputReady
  · intro equal
    funext output
    cases output
    exact equal

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
    (behavior.cycleContract.evaluateStep_allowed inputs state).1 .forward
  exact (behavior.forwardRule_holds_iff inputs state evaluated.1).mp
    holds

theorem evaluate_ready (behavior : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    let evaluated := behavior.cycleContract.evaluate inputs state
    evaluated.1 .inputReady = behavior.ready (inputs .outputReady) state := by
  intro evaluated
  have holds : behavior.readyRule.Holds inputs state evaluated.1 :=
    (behavior.cycleContract.evaluateStep_allowed inputs state).1 .ready
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

/-- Inputs observed by the upstream child of a serial composition. Readiness
from the downstream child flows backwards across the internal boundary. -/
def serialUpstreamInputs (upstream downstream : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (_upstreamState : upstream.state.Values)
    (downstreamState : downstream.state.Values) :
    (Silean.Interfaces.Fifo.ports signalType).inputs.Values
  | .inputValid => inputs .inputValid
  | .inputData => inputs .inputData
  | .outputReady => downstream.ready (inputs .outputReady) downstreamState
  | .reset => inputs .reset

/-- Inputs observed by the downstream child of a serial composition. Valid
and payload from the upstream child flow forwards across the boundary. -/
def serialDownstreamInputs (upstream downstream : CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (upstreamState : upstream.state.Values)
    (_downstreamState : downstream.state.Values) :
    (Silean.Interfaces.Fifo.ports signalType).inputs.Values
  | .inputValid =>
      (upstream.forward (inputs .inputValid) (inputs .inputData) upstreamState).1
  | .inputData =>
      (upstream.forward (inputs .inputValid) (inputs .inputData) upstreamState).2
  | .outputReady => inputs .outputReady
  | .reset => inputs .reset

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
    combineState
      (upstream.nextState
        (serialUpstreamInputs upstream downstream inputs upstreamState downstreamState)
        upstreamState)
      (downstream.nextState
        (serialDownstreamInputs upstream downstream inputs upstreamState downstreamState)
        downstreamState)

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
