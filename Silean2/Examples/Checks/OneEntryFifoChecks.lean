import Silean2.ModuleCycleEvaluation
import Silean2.Modules.OneEntryFifo

namespace Silean2.Examples.Checks.OneEntryFifo

open Silean2
open Silean2.Modules

def emptyState : (OneEntryFifo.stateMap .bit).Values
  | .storedValid | .storedData => false

def fullTrueState : (OneEntryFifo.stateMap .bit).Values
  | .storedValid | .storedData => true

def fullFalseDataState : (OneEntryFifo.stateMap .bit).Values
  | .storedValid => true
  | .storedData => false

def captureInputs : (Fifo.ports .bit).inputs.Values
  | .inputValid | .inputData => true
  | .outputReady => false

def stalledInputs : (Fifo.ports .bit).inputs.Values
  | .inputValid | .inputData | .outputReady => false

def replaceInputs : (Fifo.ports .bit).inputs.Values
  | .inputValid | .inputData | .outputReady => true

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

def vectorCaptureInputs : (Fifo.ports vectorType).inputs.Values
  | .inputValid => true
  | .inputData => vectorValue
  | .outputReady => false

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

def nestedReplaceInputs : (Fifo.ports nestedType).inputs.Values
  | .inputValid => true
  | .inputData => nestedNew
  | .outputReady => true

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

end Silean2.Examples.Checks.OneEntryFifo
