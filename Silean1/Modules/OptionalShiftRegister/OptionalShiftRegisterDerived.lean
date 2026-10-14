import Silean.Modules.ShiftRegister.Internal.ShiftRegisterVerification

/-! Public placement and correctness declarations for
`OptionalShiftRegister`. -/

namespace Silean.Modules.OptionalShiftRegister

open Silean
open Authoring.CircuitDescription

/-- Place a shift register that becomes a direct connection at latency zero. -/
noncomputable def place (latency : Nat) (input : Net signalType) :
    Builder (Net signalType) := do
  let outputs ← ShiftRegister.ports.placeIndexed signalType
    "optional_shift_register" (moduleStructure signalType latency)
    (naming signalType latency) input
  pure outputs.output

attribute [circuit_description] place

/-- The possibly empty chain has exactly one structural solution for every
input and physical state. -/
theorem structuralCertification (signalType : SignalType) (latency : Nat) :
    ModuleStructuralCertification (moduleStructure signalType latency) :=
  (certification signalType latency).structural

/-- Every structural execution satisfies the natural delayed-trace contract. -/
theorem contract_of_execution (signalType : SignalType) (latency : Nat)
    {initialState finalState : (moduleStructure signalType latency).State}
    {inputs : List (ports signalType).inputs.Values}
    {outputs : List (ports signalType).outputs.Values}
    (execution : (moduleStructure signalType latency).Executes
      initialState inputs outputs finalState) :
    contract signalType latency execution.toBoundaryTrace :=
  ShiftRegisterImplementation.Internal.optionalContract_of_execution
    signalType latency execution

end Silean.Modules.OptionalShiftRegister
