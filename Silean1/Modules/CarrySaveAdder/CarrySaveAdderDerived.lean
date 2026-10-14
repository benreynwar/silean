import Silean.Modules.CarrySaveAdder.Internal.CarrySaveAdderArithmetic
import Silean.Modules.CarrySaveAdder.Internal.CarrySaveAdderVerification

/-! Public carry-save-adder declarations backed by the indexed structural
implementation. -/

namespace Silean.Modules.CarrySaveAdder

open Silean
open Authoring.CircuitDescription

/-- Place a fixed-width carry-save adder using the next conventional indexed
name. -/
noncomputable def place (iA iB iC : Net (.vector width .bit)) :
    Builder (ports.OutputNets width) :=
  ports.placeIndexed width "carry_save_adder" (moduleStructure width)
    (naming width) iA iB iC

attribute [circuit_description] place

/-- An allowed step preserves the three-input unsigned sum modulo the fixed
vector width. -/
theorem numeric_value_of_allowed (width : Nat)
    {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step) :
    (BitVector.toNat width (step.outputs .sum) +
        BitVector.toNat width (step.outputs .carry)) %
        BitVector.cardinality width =
      totalValue width (step.inputs .iA) (step.inputs .iB) (step.inputs .iC) %
        BitVector.cardinality width := by
  rw [cycleContract.sum width allowed, cycleContract.carry width allowed]
  exact Internal.outputs_numeric_modulo width
    (step.inputs .iA) (step.inputs .iB) (step.inputs .iC)

/-- Every realizable structural step preserves the three-input unsigned sum
modulo the fixed vector width. -/
theorem numeric_value_of_realization (width : Nat)
    {step : (moduleStructure width).Step}
    (realizes : (moduleStructure width).Realizes step) :
    (BitVector.toNat width (step.outputs .sum) +
        BitVector.toNat width (step.outputs .carry)) %
        BitVector.cardinality width =
      totalValue width (step.inputs .iA) (step.inputs .iB) (step.inputs .iC) %
        BitVector.cardinality width := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification width).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification width).allows_of_realizes
      contractState step corresponds realizes
  exact numeric_value_of_allowed width allowed

/-- The indexed full-adder implementation satisfies the exact cycle contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

end Silean.Modules.CarrySaveAdder
