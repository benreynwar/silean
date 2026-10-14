import Silean.Modules.BarrelShifter.Internal.BarrelShifterVerification

/-! Public facade for the structural pipelined barrel shifter. -/

namespace Silean.Modules.BarrelShifter

open Silean
open Authoring.CircuitDescription

/-- Place a power-of-two barrel shifter with statically selected pipeline
boundaries. -/
noncomputable def place (pipeline : Pipeline exponent)
    (shift : Net (.vector exponent .bit))
    (data : Net (.vector (size exponent) element)) :
    Builder (Net (.vector (size exponent) element)) := do
  let outputs ← ports.placeIndexed element exponent "barrel_shifter"
    (moduleStructure element exponent pipeline)
    (naming element exponent pipeline) shift data
  pure outputs.result

attribute [circuit_description] place

/-- The hierarchy has exactly one structural solution for every input and
physical state. -/
theorem structuralCertification (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent) :
    ModuleStructuralCertification (moduleStructure element exponent pipeline) :=
  Internal.structuralCertification element exponent pipeline

/-- Every structural execution satisfies the natural fixed-latency rotation
contract. -/
theorem contract_of_execution (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent)
    {initialState finalState :
      (moduleStructure element exponent pipeline).State}
    {inputs : List (ports element exponent).inputs.Values}
    {outputs : List (ports element exponent).outputs.Values}
    (execution : (moduleStructure element exponent pipeline).Executes
      initialState inputs outputs finalState) :
    contract element exponent pipeline execution.toBoundaryTrace :=
  Internal.contract_of_execution element exponent pipeline execution

end Silean.Modules.BarrelShifter
