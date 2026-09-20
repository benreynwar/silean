import Silean.Modules.Mux.MuxDerived
import Silean.Semantics.StructuralExecution

namespace SileanTests.LeafwiseLogic

open Silean

def emptyState (certified : Contracts.Cycle.ModuleCycleCertified modulePorts) :
    certified.moduleStructure.State :=
  certified.moduleStructure.structuralState.defaultValues

def bitMaskInputs : (Modules.Mask.ports .bit).inputs.Values
  | .value => true
  | .mask => false

example : ∃ outputs nextState,
    (Modules.Mask.certified .bit).moduleStructure.Transition bitMaskInputs
      (emptyState (Modules.Mask.certified .bit)) outputs nextState :=
  (Modules.Mask.certified .bit).structuralCertification.hasSolution.transition_exists
    bitMaskInputs (emptyState (Modules.Mask.certified .bit))

abbrev vectorType : SignalType := .vector 3 .bit

def vectorLeft : vectorType.Denote
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => false

def vectorRight : vectorType.Denote
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false
  | ⟨2, _⟩ => true

def vectorOrInputs : (Modules.BitwiseOr.ports vectorType).inputs.Values
  | .left => vectorLeft
  | .right => vectorRight

example : ∃ outputs nextState,
    (Modules.BitwiseOr.certified vectorType).moduleStructure.Transition
      vectorOrInputs (emptyState (Modules.BitwiseOr.certified vectorType))
      outputs nextState :=
  (Modules.BitwiseOr.certified vectorType).structuralCertification.hasSolution.transition_exists
    vectorOrInputs (emptyState (Modules.BitwiseOr.certified vectorType))

abbrev nestedFields : SignalTypes :=
  .ofList [.bit, .vector 2 (.tuple (.ofList [.bit, .bit]))]

abbrev nestedType : SignalType := .tuple nestedFields

def nestedFalse : nestedType.Denote :=
  (false, (fun index => bif index = 0 then (false, (true, ()))
    else (true, (false, ())), ()))

def nestedTrue : nestedType.Denote :=
  (true, (fun index => bif index = 0 then (true, (false, ()))
    else (false, (true, ())), ()))

def nestedMuxInputs : (Modules.Mux.ports nestedType).inputs.Values
  | .select => true
  | .whenFalse => nestedFalse
  | .whenTrue => nestedTrue

example : ∃ outputs nextState,
    (Modules.Mux.certified nestedType).moduleStructure.Transition nestedMuxInputs
      (emptyState (Modules.Mux.certified nestedType)) outputs nextState :=
  (Modules.Mux.certified nestedType).structuralCertification.hasSolution.transition_exists
    nestedMuxInputs (emptyState (Modules.Mux.certified nestedType))

example {outputs nextState}
    (transition : (Modules.Mux.moduleStructure nestedType).Transition
      nestedMuxInputs (emptyState (Modules.Mux.certified nestedType))
      outputs nextState) :
    outputs .result = nestedTrue := by
  simpa [nestedMuxInputs] using
    Modules.Mux.result_of_realization nestedType transition

end SileanTests.LeafwiseLogic
