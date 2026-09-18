import Silean.Composition.SignalAdapterImplementation
import Silean.Semantics.StructuralExecution

namespace SileanTests.SignalAdapter

open Silean

def vectorValue : (SignalType.vector 2 .bit).Denote
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false

@[reducible] def vectorSplitter : Composition.SignalSplitter := .vector 2 .bit
@[reducible] def vectorCombiner : Composition.SignalCombiner := .vector 2 .bit

example : vectorSplitter.outputValues (fun | .value => vectorValue) 0 = true := rfl
example : vectorSplitter.outputValues (fun | .value => vectorValue) 1 = false := rfl
example : vectorCombiner.outputValues
    (vectorSplitter.outputValues (fun | .value => vectorValue)) .value = vectorValue := rfl

inductive NamedField
  | enabled
  | payload
deriving Enumeration

@[reducible] def namedSignals : SignalMap :=
  EnumeratedMap.of NamedField fun
    | .enabled => .bit
    | .payload => .vector 2 .bit

def tupleValue : namedSignals.tupleType.Denote :=
  namedSignals.pack fun
    | .enabled => true
    | .payload => vectorValue

@[reducible] def tupleSplitter : Composition.SignalSplitter := .tuple namedSignals.tupleFields
@[reducible] def tupleCombiner : Composition.SignalCombiner := .tuple namedSignals.tupleFields

example : tupleSplitter.outputValues (fun | .value => tupleValue) .head = true := rfl
example : tupleSplitter.outputValues (fun | .value => tupleValue) (.tail .head) = vectorValue := rfl
example : tupleCombiner.outputValues
    (tupleSplitter.outputValues (fun | .value => tupleValue)) .value = tupleValue := by
  exact tupleSplitter.combine_split tupleValue

def namedValues : namedSignals.Values
  | .enabled => true
  | .payload => vectorValue

example : namedSignals.unpack (namedSignals.pack namedValues) = namedValues := by
  simp

example (value : namedSignals.tupleType.Denote) :
    namedSignals.pack (namedSignals.unpack value) = value := by
  simp

example : namedSignals.tupleFields.get (namedSignals.pack namedValues)
    (namedSignals.tuplePosition .enabled) = true := by
  rfl

example : namedSignals.tupleFields.get (namedSignals.pack namedValues)
    (namedSignals.tuplePosition .payload) = vectorValue := by
  rfl

noncomputable def tupleSplitterState :
    tupleSplitter.certified.moduleStructure.State :=
  tupleSplitter.certified.moduleStructure.structuralState.defaultValues

noncomputable def tupleCombinerState :
    tupleCombiner.certified.moduleStructure.State :=
  tupleCombiner.certified.moduleStructure.structuralState.defaultValues

/-! Structural clients see ordinary boundary transitions. The recursive
assignment used to justify each transition remains behind `Transition`. -/

example : ∃ outputs nextState,
    tupleSplitter.certified.moduleStructure.Transition
      (fun | .value => tupleValue) tupleSplitterState outputs nextState :=
  tupleSplitter.certified.hasStructuralResult.transition_exists _ _

example : ∃ outputs nextState,
    tupleCombiner.certified.moduleStructure.Transition
      (tupleSplitter.outputValues (fun | .value => tupleValue))
      tupleCombinerState outputs nextState :=
  tupleCombiner.certified.hasStructuralResult.transition_exists _ _

example {outputs nextState otherOutputs otherNext}
    (left : tupleSplitter.certified.moduleStructure.Transition
      (fun | .value => tupleValue) tupleSplitterState outputs nextState)
    (right : tupleSplitter.certified.moduleStructure.Transition
      (fun | .value => tupleValue) tupleSplitterState otherOutputs otherNext) :
    outputs = otherOutputs ∧ nextState = otherNext :=
  left.unique tupleSplitter.certified.structuralResultUnique right

end SileanTests.SignalAdapter
