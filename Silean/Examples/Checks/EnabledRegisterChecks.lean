import Silean.Modules.EnabledRegister.EnabledRegisterCertified

namespace Silean.Examples.Checks.EnabledRegister

open Silean

example (signalType : SignalType) :
    (Modules.EnabledRegister.observeRule signalType).readsInputs.labels = [] := rfl

example (signalType : SignalType) :
    (Modules.EnabledRegister.observeRule signalType).writesOutputs.labels =
      [.q] := rfl

example (signalType : SignalType) :
    (Modules.EnabledRegister.stateRule signalType).readsInputs.labels =
      [.enable, .data] := rfl

noncomputable def structuralState (signalType : SignalType) :
    (Modules.EnabledRegister.moduleStructure signalType).State :=
  (Modules.EnabledRegister.moduleStructure signalType).structuralState.defaultValues

def bitHoldInputs : (Modules.EnabledRegister.ports .bit).inputs.Values
  | .data => true
  | .enable => false

def bitUpdateInputs : (Modules.EnabledRegister.ports .bit).inputs.Values
  | .data | .enable => true

example : ∃ proposal,
    (Modules.EnabledRegister.moduleStructure .bit).IsSolution
      bitHoldInputs (structuralState .bit) proposal ∧
    ∀ other,
      (Modules.EnabledRegister.moduleStructure .bit).IsSolution
        bitHoldInputs (structuralState .bit) other → other = proposal :=
  (Modules.EnabledRegister.certified .bit).hasExactlyOneStructuralResult _ _

example : ∃ proposal,
    (Modules.EnabledRegister.moduleStructure .bit).IsSolution
      bitUpdateInputs (structuralState .bit) proposal ∧
    ∀ other,
      (Modules.EnabledRegister.moduleStructure .bit).IsSolution
        bitUpdateInputs (structuralState .bit) other → other = proposal :=
  (Modules.EnabledRegister.certified .bit).hasExactlyOneStructuralResult _ _

abbrev vectorType : SignalType := .vector 3 .bit

def vectorValue : vectorType.Denote
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false
  | ⟨2, _⟩ => true

def vectorInputs : (Modules.EnabledRegister.ports vectorType).inputs.Values
  | .data => vectorValue
  | .enable => true

example : ∃ proposal,
    (Modules.EnabledRegister.moduleStructure vectorType).IsSolution
      vectorInputs (structuralState vectorType) proposal ∧
    ∀ other,
      (Modules.EnabledRegister.moduleStructure vectorType).IsSolution
        vectorInputs (structuralState vectorType) other → other = proposal :=
  (Modules.EnabledRegister.certified vectorType).hasExactlyOneStructuralResult _ _

abbrev nestedFields : SignalTypes :=
  .ofList [.bit, .vector 2 (.tuple (.ofList [.bit, .bit]))]

abbrev nestedType : SignalType := .tuple nestedFields

def nestedValue : nestedType.Denote :=
  (true, (fun index => bif index = 0 then (false, (true, ()))
    else (true, (false, ())), ()))

def nestedInputs : (Modules.EnabledRegister.ports nestedType).inputs.Values
  | .data => nestedValue
  | .enable => true

example : ∃ proposal,
    (Modules.EnabledRegister.moduleStructure nestedType).IsSolution
      nestedInputs (structuralState nestedType) proposal ∧
    ∀ other,
      (Modules.EnabledRegister.moduleStructure nestedType).IsSolution
        nestedInputs (structuralState nestedType) other → other = proposal :=
  (Modules.EnabledRegister.certified nestedType).hasExactlyOneStructuralResult _ _

example : ∃ contractState,
    (Modules.EnabledRegister.certified nestedType).stateCorresponds contractState
      (structuralState nestedType) :=
  (Modules.EnabledRegister.certified nestedType).hasCorrespondingState _

end Silean.Examples.Checks.EnabledRegister
