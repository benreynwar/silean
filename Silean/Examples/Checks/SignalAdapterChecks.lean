import Silean.Composition.SignalAdapterImplementation

namespace Silean.Examples.Checks.SignalAdapter

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

def tupleFields : SignalTypes :=
  .ofList [.bit, .vector 2 .bit]

def tupleValue : (SignalType.tuple tupleFields).Denote :=
  (true, (vectorValue, ()))

@[reducible] def tupleSplitter : Composition.SignalSplitter := .tuple tupleFields
@[reducible] def tupleCombiner : Composition.SignalCombiner := .tuple tupleFields

example : tupleCombiner.outputValues
    (tupleSplitter.outputValues (fun | .value => tupleValue)) .value = tupleValue :=
  SignalTypes.assemble_get tupleFields tupleValue

def emptyComponentState : emptySignalMap.Values := SignalMap.emptyValues

example : ∃ proposal,
    vectorSplitter.certified.moduleStructure.IsSolution
      (fun | .value => vectorValue) emptyComponentState proposal :=
  vectorSplitter.certified.hasStructuralResult _ _

example : ∃ proposal,
    tupleSplitter.certified.moduleStructure.IsSolution
      (fun | .value => tupleValue) emptyComponentState proposal ∧
    ∀ other,
      tupleSplitter.certified.moduleStructure.IsSolution
        (fun | .value => tupleValue) emptyComponentState other → other = proposal :=
  tupleSplitter.certified.hasExactlyOneStructuralResult _ _

end Silean.Examples.Checks.SignalAdapter
