import Silean.Modules.ShiftRegister.Internal.ShiftRegisterVerification

/-! Public placement and correctness declarations for `ShiftRegister`. -/

namespace Silean.Modules.ShiftRegister

open Silean
open Authoring.CircuitDescription

/-- Place a positive-latency shift register. -/
noncomputable def place (latency : Nat) (positive : 0 < latency)
    (input : Net signalType) : Builder (Net signalType) := do
  let outputs ← ports.placeIndexed signalType "shift_register"
    (moduleStructure signalType latency positive)
    (naming signalType latency positive) input
  pure outputs.output

attribute [circuit_description] place

/-- The register chain has exactly one structural solution for every input and
physical state. -/
theorem structuralCertification (signalType : SignalType) (latency : Nat)
    (positive : 0 < latency) :
    ModuleStructuralCertification
      (moduleStructure signalType latency positive) :=
  (certification signalType latency positive).structural

/-- Every structural execution satisfies the natural delayed-trace contract. -/
theorem contract_of_execution (signalType : SignalType) (latency : Nat)
    (positive : 0 < latency)
    {initialState finalState :
      (moduleStructure signalType latency positive).State}
    {inputs : List (ports signalType).inputs.Values}
    {outputs : List (ports signalType).outputs.Values}
    (execution : (moduleStructure signalType latency positive).Executes
      initialState inputs outputs finalState) :
    contract signalType latency positive execution.toBoundaryTrace := by
  simpa [contract, OptionalShiftRegister.contract] using
    ShiftRegisterImplementation.Internal.optionalContract_of_execution
      signalType latency execution

end Silean.Modules.ShiftRegister
