import Silean.Modules.Register.Register

namespace Silean.Examples.Checks.Register

open Silean

abbrev vectorType : SignalType := .vector 2 .bit

def vectorInput : vectorType.Denote
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false

def vectorInputs : (Modules.Register.ports vectorType).inputs.Values
  | .input => vectorInput

noncomputable def vectorStructuralState :
    (Modules.Register.certified vectorType).moduleStructure.State :=
  (Modules.Register.certified vectorType).moduleStructure.structuralState.defaultValues

example : ∃ proposal,
    (Modules.Register.certified vectorType).moduleStructure.IsSolution
      vectorInputs vectorStructuralState proposal :=
  (Modules.Register.certified vectorType).hasStructuralResult _ _

example : ∃ proposal,
    (Modules.Register.certified vectorType).moduleStructure.IsSolution
      vectorInputs vectorStructuralState proposal ∧
    ∀ other,
      (Modules.Register.certified vectorType).moduleStructure.IsSolution
        vectorInputs vectorStructuralState other → other = proposal :=
  (Modules.Register.certified vectorType).hasExactlyOneStructuralResult _ _

abbrev tupleFields : SignalTypes :=
  .ofList [.bit, .vector 2 (.tuple (.ofList [.bit, .bit]))]

abbrev tupleType : SignalType := .tuple tupleFields

def tupleInput : tupleType.Denote :=
  (true, (fun index => bif index = 0 then (true, (false, ()))
    else (false, (true, ())), ()))

def tupleInputs : (Modules.Register.ports tupleType).inputs.Values
  | .input => tupleInput

noncomputable def tupleStructuralState :
    (Modules.Register.certified tupleType).moduleStructure.State :=
  (Modules.Register.certified tupleType).moduleStructure.structuralState.defaultValues

example : ∃ proposal,
    (Modules.Register.certified tupleType).moduleStructure.IsSolution
      tupleInputs tupleStructuralState proposal ∧
    ∀ other,
      (Modules.Register.certified tupleType).moduleStructure.IsSolution
        tupleInputs tupleStructuralState other → other = proposal :=
  (Modules.Register.certified tupleType).hasExactlyOneStructuralResult _ _

end Silean.Examples.Checks.Register
