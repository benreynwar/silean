import Silean.Modules.EnabledRegister.EnabledRegisterDerived
import Silean.Semantics.StructuralExecution

namespace SileanTests.EnabledRegister

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

example : ∃ outputs nextState,
    (Modules.EnabledRegister.moduleStructure .bit).Transition bitHoldInputs
      (structuralState .bit) outputs nextState :=
  (Modules.EnabledRegister.certified .bit).structuralCertification.hasSolution.transition_exists
    bitHoldInputs (structuralState .bit)

example : ∃ outputs nextState,
    (Modules.EnabledRegister.moduleStructure .bit).Transition bitUpdateInputs
      (structuralState .bit) outputs nextState :=
  (Modules.EnabledRegister.certified .bit).structuralCertification.hasSolution.transition_exists
    bitUpdateInputs (structuralState .bit)

abbrev vectorType : SignalType := .vector 3 .bit

def vectorValue : vectorType.Denote
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false
  | ⟨2, _⟩ => true

def vectorInputs : (Modules.EnabledRegister.ports vectorType).inputs.Values
  | .data => vectorValue
  | .enable => true

example : ∃ outputs nextState,
    (Modules.EnabledRegister.moduleStructure vectorType).Transition vectorInputs
      (structuralState vectorType) outputs nextState :=
  (Modules.EnabledRegister.certified vectorType).structuralCertification.hasSolution.transition_exists
    vectorInputs (structuralState vectorType)

abbrev nestedFields : SignalTypes :=
  .ofList [.bit, .vector 2 (.tuple (.ofList [.bit, .bit]))]

abbrev nestedType : SignalType := .tuple nestedFields

def nestedValue : nestedType.Denote :=
  (true, (fun index => bif index = 0 then (false, (true, ()))
    else (true, (false, ())), ()))

def nestedInputs : (Modules.EnabledRegister.ports nestedType).inputs.Values
  | .data => nestedValue
  | .enable => true

example : ∃ outputs nextState,
    (Modules.EnabledRegister.moduleStructure nestedType).Transition nestedInputs
      (structuralState nestedType) outputs nextState :=
  (Modules.EnabledRegister.certified nestedType).structuralCertification.hasSolution.transition_exists
    nestedInputs (structuralState nestedType)

example : ∃ contractState,
    (Modules.EnabledRegister.certified nestedType).stateCorresponds contractState
      (structuralState nestedType) :=
  (Modules.EnabledRegister.certified nestedType).hasCorrespondingState _

/-! The two reader-facing correctness links are available without importing
the structural proof files directly. -/

example :
    (Modules.EnabledRegister.description .bit).ImplementsCycleContract
      (Modules.EnabledRegister.cycleContract .bit)
      (Modules.EnabledRegister.Naming.ports .bit) :=
  Modules.EnabledRegister.construction_correct .bit

example : Contracts.Cycle.Implements
    (Modules.EnabledRegister.moduleStructure .bit)
    (Modules.EnabledRegister.cycleContract .bit)
    (Modules.EnabledRegister.certification .bit).stateCorresponds :=
  Modules.EnabledRegister.implements_contract .bit

end SileanTests.EnabledRegister
