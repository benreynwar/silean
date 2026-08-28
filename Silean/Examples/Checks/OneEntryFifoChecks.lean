import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Modules.OneEntryFifo.OneEntryFifo

namespace Silean.Examples.Checks.OneEntryFifo

open Silean
open Silean.Modules

def emptyState : (OneEntryFifo.stateMap .bit).Values
  | .storedValid | .storedData => false

def fullTrueState : (OneEntryFifo.stateMap .bit).Values
  | .storedValid | .storedData => true

def fullFalseDataState : (OneEntryFifo.stateMap .bit).Values
  | .storedValid => true
  | .storedData => false

def captureInputs : (Silean.Interfaces.Fifo.ports .bit).inputs.Values
  | .inputValid | .inputData => true
  | .outputReady | .reset => false

def stalledInputs : (Silean.Interfaces.Fifo.ports .bit).inputs.Values
  | .inputValid | .inputData | .outputReady | .reset => false

def replaceInputs : (Silean.Interfaces.Fifo.ports .bit).inputs.Values
  | .inputValid | .inputData | .outputReady => true
  | .reset => false

def resetInputs : (Silean.Interfaces.Fifo.ports .bit).inputs.Values
  | .inputValid | .outputReady => false
  | .inputData | .reset => true

/-! An empty FIFO is fall-through and simultaneously captures an unaccepted
input when the downstream is not ready. -/

example : ((OneEntryFifo.cycleContract .bit).evaluate captureInputs emptyState).1
    .outputValid = true := rfl

example : ((OneEntryFifo.cycleContract .bit).evaluate captureInputs emptyState).1
    .outputData = true := rfl

example : ((OneEntryFifo.cycleContract .bit).evaluate captureInputs emptyState).1
    .inputReady = true := rfl

example : ((OneEntryFifo.cycleContract .bit).evaluate captureInputs emptyState).2
    .storedValid = true := rfl

example : ((OneEntryFifo.cycleContract .bit).evaluate captureInputs emptyState).2
    .storedData = true := rfl

/-! Backpressure holds both occupied state fields and deasserts input ready. -/

example : ((OneEntryFifo.cycleContract .bit).evaluate stalledInputs fullTrueState).1
    .inputReady = false := rfl

example : ((OneEntryFifo.cycleContract .bit).evaluate stalledInputs fullTrueState).2 =
    fullTrueState := by
  funext state
  cases state <;> rfl

/-! A ready downstream dequeues the stored word while a simultaneous valid
input replaces it. Observable data for that cycle is still the older word. -/

example : ((OneEntryFifo.cycleContract .bit).evaluate replaceInputs fullFalseDataState).1
    .outputData = false := rfl

example : ((OneEntryFifo.cycleContract .bit).evaluate replaceInputs fullFalseDataState).2
    .storedValid = true := rfl

example : ((OneEntryFifo.cycleContract .bit).evaluate replaceInputs fullFalseDataState).2
    .storedData = true := rfl

/-! Reset is synchronous: outputs still observe the old state in the reset
cycle, but the following valid state is empty. Payload storage is deliberately
not reset and may retain its previous value. -/

example : ((OneEntryFifo.cycleContract .bit).evaluate resetInputs fullTrueState).1
    .outputValid = true := rfl

example : ((OneEntryFifo.cycleContract .bit).evaluate resetInputs fullTrueState).2
    .storedValid = false := rfl

example : ((OneEntryFifo.cycleContract .bit).evaluate resetInputs fullTrueState).2
    .storedData = true := rfl

/-! The same certified FIFO carries aggregate payloads without changing its
bit-valued valid/ready protocol. -/

noncomputable def structuralState (signalType : SignalType) :
    (OneEntryFifo.moduleStructure signalType).State :=
  (OneEntryFifo.moduleStructure signalType).structuralState.defaultValues

abbrev vectorType : SignalType := .vector 3 .bit

def vectorValue : vectorType.Denote
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false
  | ⟨2, _⟩ => true

def vectorEmptyState : (OneEntryFifo.stateMap vectorType).Values
  | .storedValid => false
  | .storedData => fun _ => false

def vectorCaptureInputs : (Silean.Interfaces.Fifo.ports vectorType).inputs.Values
  | .inputValid => true
  | .inputData => vectorValue
  | .outputReady | .reset => false

example : ((OneEntryFifo.cycleContract vectorType).evaluate
    vectorCaptureInputs vectorEmptyState).1 .outputData = vectorValue := rfl

example : ((OneEntryFifo.cycleContract vectorType).evaluate
    vectorCaptureInputs vectorEmptyState).2 .storedData = vectorValue := rfl

example : ∃ proposal,
    (OneEntryFifo.moduleStructure vectorType).IsSolution
      vectorCaptureInputs (structuralState vectorType) proposal ∧
    ∀ other,
      (OneEntryFifo.moduleStructure vectorType).IsSolution
        vectorCaptureInputs (structuralState vectorType) other → other = proposal :=
  (OneEntryFifo.certified vectorType).hasExactlyOneStructuralResult _ _

abbrev nestedFields : SignalTypes :=
  .ofList [.bit, .vector 2 (.tuple (.ofList [.bit, .bit]))]

abbrev nestedType : SignalType := .tuple nestedFields

def nestedOld : nestedType.Denote :=
  (false, (fun index => bif index = 0 then (false, (true, ()))
    else (true, (false, ())), ()))

def nestedNew : nestedType.Denote :=
  (true, (fun index => bif index = 0 then (true, (false, ()))
    else (false, (true, ())), ()))

def nestedFullState : (OneEntryFifo.stateMap nestedType).Values
  | .storedValid => true
  | .storedData => nestedOld

def nestedReplaceInputs : (Silean.Interfaces.Fifo.ports nestedType).inputs.Values
  | .inputValid => true
  | .inputData => nestedNew
  | .outputReady => true
  | .reset => false

example : ((OneEntryFifo.cycleContract nestedType).evaluate
    nestedReplaceInputs nestedFullState).1 .outputData = nestedOld := rfl

example : ((OneEntryFifo.cycleContract nestedType).evaluate
    nestedReplaceInputs nestedFullState).2 .storedData = nestedNew := rfl

example : ∃ proposal,
    (OneEntryFifo.moduleStructure nestedType).IsSolution
      nestedReplaceInputs (structuralState nestedType) proposal ∧
    ∀ other,
      (OneEntryFifo.moduleStructure nestedType).IsSolution
        nestedReplaceInputs (structuralState nestedType) other → other = proposal :=
  (OneEntryFifo.certified nestedType).hasExactlyOneStructuralResult _ _

example : ∃ contractState,
    (OneEntryFifo.certified nestedType).stateCorresponds contractState
      (structuralState nestedType) :=
  (OneEntryFifo.certified nestedType).hasCorrespondingState _

end Silean.Examples.Checks.OneEntryFifo
