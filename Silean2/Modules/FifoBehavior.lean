import Silean2.Modules.OneEntryFifo

namespace Silean2.Modules.Fifo

open Silean2

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

structure Behavior (signalType : SignalType) where
  state : SignalMap
  forward : Bool → signalType.Denote → state.Values →
    Bool × signalType.Denote
  ready : Bool → state.Values → Bool
  nextState : (OneEntryFifo.ports signalType).inputs.Values →
    state.Values → state.Values

namespace Behavior

def forwardRule (behavior : Behavior signalType) :
    CycleOutputRule (OneEntryFifo.ports signalType) behavior.state
      (.ofLists [.bit, signalType] [.bit, signalType]) where
  readsInputs := ((OneEntryFifo.inputMap signalType).select .inputData).prepend
    .inputValid
  writesOutputs := ((OneEntryFifo.outputMap signalType).select .outputData).prepend
    .outputValid
  target
    | (inputValid, (inputData, ())), state =>
        let result := behavior.forward inputValid inputData state
        (result.1, (result.2, ()))

def readyRule (behavior : Behavior signalType) :
    CycleOutputRule (OneEntryFifo.ports signalType) behavior.state
      (.ofLists [.bit] [.bit]) where
  readsInputs := (OneEntryFifo.inputMap signalType).select .outputReady
  writesOutputs := (OneEntryFifo.outputMap signalType).select .inputReady
  target
    | (outputReady, ()), state => (behavior.ready outputReady state, ())

def stateRule (behavior : Behavior signalType) :
    CycleStateRule (OneEntryFifo.ports signalType) behavior.state where
  inputTypes := .cons .bit (.cons .bit (.cons signalType .nil))
  readsInputs :=
    (((OneEntryFifo.inputMap signalType).select .inputData).prepend .inputValid).prepend
      .outputReady
  target
    | (outputReady, (inputValid, (inputData, ()))), state =>
        behavior.nextState (fun
          | .inputValid => inputValid
          | .inputData => inputData
          | .outputReady => outputReady) state

def cycleContract (behavior : Behavior signalType) :
    ModuleCycleContract (OneEntryFifo.ports signalType) where
  state := behavior.state
  RuleName := OneEntryFifo.Rule
  ruleNames := inferInstance
  outputRule
    | .forward => ⟨_, behavior.forwardRule⟩
    | .ready => ⟨_, behavior.readyRule⟩
  stateRule := behavior.stateRule
  outputCoverage := by rfl

@[simp] theorem stateRule_apply (behavior : Behavior signalType)
    (inputs : (OneEntryFifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    behavior.stateRule.apply inputs state = behavior.nextState inputs state := by
  simp only [stateRule, CycleStateRule.apply, SignalSelection.project,
    SignalSelection.prepend, SignalMap.select]
  congr 1
  funext input
  cases input <;> rfl

@[simp] theorem cycleContract_stateRule_apply (behavior : Behavior signalType)
    (inputs : (OneEntryFifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    behavior.cycleContract.stateRule.apply inputs state =
      behavior.nextState inputs state :=
  behavior.stateRule_apply inputs state

@[simp] theorem cycleContract_forward_reads (behavior : Behavior signalType) :
    ((behavior.cycleContract.outputRule OneEntryFifo.Rule.forward).2.readsInputs.labels) =
      [.inputValid, .inputData] := rfl

@[simp] theorem cycleContract_forward_writes (behavior : Behavior signalType) :
    ((behavior.cycleContract.outputRule OneEntryFifo.Rule.forward).2.writesOutputs.labels) =
      [.outputValid, .outputData] := rfl

@[simp] theorem cycleContract_ready_reads (behavior : Behavior signalType) :
    ((behavior.cycleContract.outputRule OneEntryFifo.Rule.ready).2.readsInputs.labels) =
      [.outputReady] := rfl

@[simp] theorem cycleContract_ready_writes (behavior : Behavior signalType) :
    ((behavior.cycleContract.outputRule OneEntryFifo.Rule.ready).2.writesOutputs.labels) =
      [.inputReady] := rfl

theorem forwardRule_holds_iff (behavior : Behavior signalType)
    (inputs : (OneEntryFifo.ports signalType).inputs.Values)
    (state : behavior.state.Values)
    (outputs : (OneEntryFifo.ports signalType).outputs.Values) :
    behavior.forwardRule.Holds inputs state outputs ↔
      outputs .outputValid =
          (behavior.forward (inputs .inputValid) (inputs .inputData) state).1 ∧
      outputs .outputData =
          (behavior.forward (inputs .inputValid) (inputs .inputData) state).2 := by
  simp [CycleOutputRule.Holds, forwardRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]

theorem readyRule_holds_iff (behavior : Behavior signalType)
    (inputs : (OneEntryFifo.ports signalType).inputs.Values)
    (state : behavior.state.Values)
    (outputs : (OneEntryFifo.ports signalType).outputs.Values) :
    behavior.readyRule.Holds inputs state outputs ↔
      outputs .inputReady = behavior.ready (inputs .outputReady) state := by
  simp [CycleOutputRule.Holds, readyRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

theorem evaluate_forward (behavior : Behavior signalType)
    (inputs : (OneEntryFifo.ports signalType).inputs.Values)
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

theorem evaluate_ready (behavior : Behavior signalType)
    (inputs : (OneEntryFifo.ports signalType).inputs.Values)
    (state : behavior.state.Values) :
    let evaluated := behavior.cycleContract.evaluate inputs state
    evaluated.1 .inputReady = behavior.ready (inputs .outputReady) state := by
  intro evaluated
  have holds : behavior.readyRule.Holds inputs state evaluated.1 :=
    (behavior.cycleContract.evaluate_evaluatesTo inputs state).1 .ready
  exact (behavior.readyRule_holds_iff inputs state evaluated.1).mp
    holds

def serial (upstream downstream : Behavior signalType) : Behavior signalType where
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
    let upstreamInputs : (OneEntryFifo.ports signalType).inputs.Values := fun
      | .inputValid => inputs .inputValid
      | .inputData => inputs .inputData
      | .outputReady => middleReady
    let downstreamInputs : (OneEntryFifo.ports signalType).inputs.Values := fun
      | .inputValid => middle.1
      | .inputData => middle.2
      | .outputReady => inputs .outputReady
    combineState (upstream.nextState upstreamInputs upstreamState)
      (downstream.nextState downstreamInputs downstreamState)

end Behavior

structure CertifiedBehavior (signalType : SignalType) where
  behavior : Behavior signalType
  moduleStructure : ModuleStructure (OneEntryFifo.ports signalType)
  certification : ModuleCycleCertification moduleStructure behavior.cycleContract

def CertifiedBehavior.certified (value : CertifiedBehavior signalType) :
    ModuleCycleCertified (OneEntryFifo.ports signalType) :=
  value.certification.bundle

@[simp] theorem CertifiedBehavior.certified_cycleContract
    (value : CertifiedBehavior signalType) :
    value.certified.cycleContract = value.behavior.cycleContract := rfl

@[simp] theorem CertifiedBehavior.certified_stateRule_apply
    (value : CertifiedBehavior signalType)
    (inputs : (OneEntryFifo.ports signalType).inputs.Values)
    (state : value.certified.cycleContract.state.Values) :
    value.certified.cycleContract.stateRule.apply inputs state =
      value.behavior.nextState inputs state := by
  change value.behavior.cycleContract.stateRule.apply inputs state = _
  exact value.behavior.cycleContract_stateRule_apply inputs state

def oneEntryBehavior (signalType : SignalType) : Behavior signalType where
  state := OneEntryFifo.stateMap signalType
  forward := fun inputValid inputData state =>
    (state .storedValid || inputValid,
      bif state .storedValid then state .storedData else inputData)
  ready := fun outputReady state => outputReady || !state .storedValid
  nextState := (OneEntryFifo.stateRule signalType).apply

theorem oneEntryBehavior_cycleContract (signalType : SignalType) :
    (oneEntryBehavior signalType).cycleContract =
      OneEntryFifo.cycleContract signalType := rfl

noncomputable def oneEntryCertified (signalType : SignalType) :
    CertifiedBehavior signalType where
  behavior := oneEntryBehavior signalType
  moduleStructure := OneEntryFifo.moduleStructure signalType
  certification := (OneEntryFifo.certification signalType).transportContract
    (oneEntryBehavior_cycleContract signalType).symm

end Silean2.Modules.Fifo
