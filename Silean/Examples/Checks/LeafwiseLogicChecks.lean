import Silean.Modules.Mux

namespace Silean.Examples.Checks.LeafwiseLogic

open Silean

def emptyState (certified : ModuleCycleCertified modulePorts) :
    certified.moduleStructure.State :=
  certified.moduleStructure.structuralState.defaultValues

def bitMaskInputs : (Modules.Mask.ports .bit).inputs.Values
  | .value => true
  | .mask => false

example : ∃ proposal,
    (Modules.Mask.certified .bit).moduleStructure.IsSolution
      bitMaskInputs (emptyState (Modules.Mask.certified .bit)) proposal ∧
    ∀ other,
      (Modules.Mask.certified .bit).moduleStructure.IsSolution
        bitMaskInputs (emptyState (Modules.Mask.certified .bit)) other →
      other = proposal :=
  (Modules.Mask.certified .bit).hasExactlyOneStructuralResult _ _

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

example : ∃ proposal,
    (Modules.BitwiseOr.certified vectorType).moduleStructure.IsSolution
      vectorOrInputs (emptyState (Modules.BitwiseOr.certified vectorType)) proposal ∧
    ∀ other,
      (Modules.BitwiseOr.certified vectorType).moduleStructure.IsSolution
        vectorOrInputs (emptyState (Modules.BitwiseOr.certified vectorType)) other →
      other = proposal :=
  (Modules.BitwiseOr.certified vectorType).hasExactlyOneStructuralResult _ _

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

example : ∃ proposal,
    (Modules.Mux.certified nestedType).moduleStructure.IsSolution
      nestedMuxInputs (emptyState (Modules.Mux.certified nestedType)) proposal ∧
    ∀ other,
      (Modules.Mux.certified nestedType).moduleStructure.IsSolution
        nestedMuxInputs (emptyState (Modules.Mux.certified nestedType)) other →
      other = proposal :=
  (Modules.Mux.certified nestedType).hasExactlyOneStructuralResult _ _

end Silean.Examples.Checks.LeafwiseLogic
