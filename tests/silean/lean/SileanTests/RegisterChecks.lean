import Silean.Modules.Register.RegisterTheorems
import Silean.Semantics.StructuralExecution

namespace SileanTests.Register

open Silean

abbrev vectorType : SignalType := .vector 2 .bit

def vectorInput : vectorType.Denote
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false

def vectorInputs : (Modules.Register.ports vectorType).inputs.Values
  | .input => vectorInput

def vectorContractState : (Modules.Register.stateMap vectorType).Values
  | .stored => fun _ => false

/-! The public Step laws capture the two defining facts about a register: it
shows the old value now and stores the input for the next cycle. -/

example : ((Modules.Register.cycleContract vectorType).evaluateStep
    vectorInputs vectorContractState).outputs .output =
    vectorContractState .stored :=
  Modules.Register.output_of_allowed
    ((Modules.Register.cycleContract vectorType).evaluateStep_allowed _ _)

example : ((Modules.Register.cycleContract vectorType).evaluateStep
    vectorInputs vectorContractState).nextState .stored = vectorInput :=
  Modules.Register.next_stored_of_allowed
    ((Modules.Register.cycleContract vectorType).evaluateStep_allowed _ _)

noncomputable def vectorStructuralState :
    (Modules.Register.certified vectorType).moduleStructure.State :=
  (Modules.Register.certified vectorType).moduleStructure.structuralState.defaultValues

example : ∃ outputs nextState,
    (Modules.Register.certified vectorType).moduleStructure.Transition
      vectorInputs vectorStructuralState outputs nextState :=
  (Modules.Register.certified vectorType).hasStructuralResult.transition_exists
    vectorInputs vectorStructuralState

example {outputs nextState otherOutputs otherNext}
    (left : (Modules.Register.certified vectorType).moduleStructure.Transition
      vectorInputs vectorStructuralState outputs nextState)
    (right : (Modules.Register.certified vectorType).moduleStructure.Transition
      vectorInputs vectorStructuralState otherOutputs otherNext) :
    outputs = otherOutputs ∧ nextState = otherNext :=
  left.unique (Modules.Register.certified vectorType).structuralResultUnique right

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

example : ∃ outputs nextState,
    (Modules.Register.certified tupleType).moduleStructure.Transition
      tupleInputs tupleStructuralState outputs nextState :=
  (Modules.Register.certified tupleType).hasStructuralResult.transition_exists
    tupleInputs tupleStructuralState

end SileanTests.Register
