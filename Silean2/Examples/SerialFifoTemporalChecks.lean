import Silean2.Contracts.NoResetFifoSerialExecution
import Silean2.Modules.OneEntryFifoTemporal

namespace Silean2.Examples.SerialFifoTemporalChecks

open Silean2.Contracts
open Silean2.Modules

abbrev StageState (signalType : SignalType) :=
  OneEntryFifo.Temporal.ContractState signalType

abbrev TwoStageState (signalType : SignalType) :=
  StageState signalType × StageState signalType

def childInputs (signalType : SignalType)
    (state : TwoStageState signalType)
    (input : NoResetFifo.Execution.Input signalType.Denote) :
    NoResetFifo.Execution.Input signalType.Denote ×
      NoResetFifo.Execution.Input signalType.Denote :=
  let downstreamProbe := OneEntryFifo.Temporal.step signalType state.2
    { enqValid := false, enqData := signalType.default,
      deqReady := input.deqReady }
  let upstreamInput : NoResetFifo.Execution.Input signalType.Denote :=
    { enqValid := input.enqValid, enqData := input.enqData,
      deqReady := downstreamProbe.cycle.enqReady }
  let upstreamStep := OneEntryFifo.Temporal.step signalType state.1 upstreamInput
  let downstreamInput : NoResetFifo.Execution.Input signalType.Denote :=
    { enqValid := upstreamStep.cycle.deqValid
      enqData := upstreamStep.cycle.deqData
      deqReady := input.deqReady }
  (upstreamInput, downstreamInput)

def step (signalType : SignalType) (state : TwoStageState signalType)
    (input : NoResetFifo.Execution.Input signalType.Denote) :
    NoResetFifo.Execution.StepResult (TwoStageState signalType)
      signalType.Denote :=
  let children := childInputs signalType state input
  let upstream := OneEntryFifo.Temporal.step signalType state.1 children.1
  let downstream := OneEntryFifo.Temporal.step signalType state.2 children.2
  { nextState := (upstream.nextState, downstream.nextState)
    cycle :=
      { enqValid := upstream.cycle.enqValid
        enqData := upstream.cycle.enqData
        enqReady := upstream.cycle.enqReady
        deqValid := downstream.cycle.deqValid
        deqData := downstream.cycle.deqData
        deqReady := downstream.cycle.deqReady } }

def model (signalType : SignalType) :
    NoResetFifo.Execution.Model (TwoStageState signalType)
      signalType.Denote where
  step := step signalType

theorem step_decomposes (signalType : SignalType)
    (state : TwoStageState signalType)
    (input : NoResetFifo.Execution.Input signalType.Denote) :
    NoResetFifo.Execution.StepDecomposition
      (model signalType)
      (OneEntryFifo.Temporal.model signalType)
      (OneEntryFifo.Temporal.model signalType)
      Prod.fst Prod.snd (childInputs signalType) state input := by
  constructor
  · rfl
  · rfl
  · constructor <;>
      simp [model, step, childInputs, OneEntryFifo.Temporal.model]

def serialExecution (signalType : SignalType) :
    NoResetFifo.Execution.Serial
      (model signalType)
      (OneEntryFifo.Temporal.model signalType)
      (OneEntryFifo.Temporal.model signalType) where
  upstreamState := Prod.fst
  downstreamState := Prod.snd
  childInputs := childInputs signalType
  step_decomposes := step_decomposes signalType

def contents (state : TwoStageState signalType) : List signalType.Denote :=
  OneEntryFifo.Temporal.contents state.2 ++
    OneEntryFifo.Temporal.contents state.1

def fifoView (signalType : SignalType) :
    NoResetFifo.ModuleView (TwoStageState signalType) signalType.Denote where
  contents := contents
  capacity := 2
  readyPropagationLatency := 0
  contents_bounded := by
    intro state
    simp only [contents, List.length_append]
    have upstream := OneEntryFifo.Temporal.contents_capacity_one state.1
    have downstream := OneEntryFifo.Temporal.contents_capacity_one state.2
    omega

def constructor (signalType : SignalType) :
    NoResetFifo.ModuleView.Execution.Constructor
      (fifoView signalType)
      (OneEntryFifo.Temporal.fifoView signalType)
      (OneEntryFifo.Temporal.fifoView signalType)
      (model signalType)
      (OneEntryFifo.Temporal.model signalType)
      (OneEntryFifo.Temporal.model signalType) where
  serial := serialExecution signalType
  contents := fun _ => rfl

theorem fifoView_satisfies (signalType : SignalType) :
    NoResetFifo.ModuleView.Satisfies (fifoView signalType)
      (constructor signalType).outerExecutes :=
  (constructor signalType).satisfies rfl rfl
    (OneEntryFifo.Temporal.fifoView_satisfies signalType)
    (OneEntryFifo.Temporal.fifoView_satisfies signalType)

def payloadType : SignalType :=
  .tuple (.cons (.vector 3 .bit) (.cons .bit .nil))

example : NoResetFifo.ModuleView.Satisfies (fifoView payloadType)
    (constructor payloadType).outerExecutes :=
  fifoView_satisfies payloadType

-- Each temporal child is backed by the already certified structure.
example
    (inputs : (OneEntryFifo.ports payloadType).inputs.Values)
    (contractState :
      (OneEntryFifo.certified payloadType).cycleContract.state.Values)
    (structuralState :
      (OneEntryFifo.certified payloadType).moduleStructure.State)
    (proposal :
      ProposedValues (OneEntryFifo.certified payloadType).moduleStructure)
    (corresponds : (OneEntryFifo.certified payloadType).stateCorresponds
      contractState structuralState)
    (satisfies : (OneEntryFifo.certified payloadType).moduleStructure.IsSolution
      inputs structuralState proposal) :
    proposal.outputs =
        ((OneEntryFifo.certified payloadType).cycleContract.evaluate
          inputs contractState).1 ∧
      (OneEntryFifo.certified payloadType).stateCorresponds
        ((OneEntryFifo.certified payloadType).cycleContract.evaluate
          inputs contractState).2 proposal.nextState :=
  (OneEntryFifo.certified payloadType).solution_matches_evaluate
    inputs contractState structuralState proposal corresponds satisfies

end Silean2.Examples.SerialFifoTemporalChecks
