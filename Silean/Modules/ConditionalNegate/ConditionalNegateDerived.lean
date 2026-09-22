import Silean.Modules.ConditionalNegate.Internal.ConditionalNegateVerification

/-! Public conditional-negation declarations backed by the authored
construction and generated structural proof. -/

namespace Silean.Modules.ConditionalNegate

open Silean
open Authoring.CircuitDescription

/-- Place a conditional negator using the next conventional indexed name. -/
noncomputable def place (value : Net (.vector width .bit))
    (negate : Net .bit) : Builder (ports.OutputNets width) :=
  ports.placeIndexed width "conditional_negate" (moduleStructure width)
    (naming width) value negate

attribute [circuit_description] place

/-- Every typed implementation corresponding to the authored construction
implements the conditional-negation contract. -/
theorem construction_correct (width : Nat) :
    (description width).ImplementsCycleContract (cycleContract width)
      (Naming.ports width) :=
  Internal.construction_correct width

/-- The generated structural conditional negator implements its cycle
contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

/-- Every structural realization has the contract's native fixed-width
interpretation. -/
theorem result_toBitVec_of_realization (width : Nat)
    {step : (moduleStructure width).Step}
    (realizes : (moduleStructure width).Realizes step) :
    BitVector.toBitVec width (step.outputs .result) =
      bif step.inputs .negate then
        -BitVector.toBitVec width (step.inputs .value)
      else
        BitVector.toBitVec width (step.inputs .value) := by
  obtain ⟨_, _, allowed⟩ := allowed_of_realization width realizes
  exact result_toBitVec_of_allowed width allowed

end Silean.Modules.ConditionalNegate
