import Silean.Modules.PartialProductRow.Internal.PartialProductRowArithmetic
import Silean.Modules.PartialProductRow.Internal.PartialProductRowVerification

/-! Public partial-product-row declarations backed by generated internals. -/

namespace Silean.Modules.PartialProductRow

open Silean
open Authoring.CircuitDescription

noncomputable def place (row : Fin multiplierWidth)
    (multiplicand : Net (.vector multiplicandWidth .bit))
    (select : Net .bit) :
    Builder (Net (.vector (multiplicandWidth + multiplierWidth) .bit)) := do
  let outputs ← ports.placeIndexed multiplicandWidth multiplierWidth
    "partial_product_row"
    (moduleStructure multiplicandWidth multiplierWidth row)
    (naming multiplicandWidth multiplierWidth row) multiplicand select
  pure outputs.result

attribute [circuit_description] place

theorem construction_correct (multiplicandWidth multiplierWidth : Nat)
    (row : Fin multiplierWidth) :
    (description multiplicandWidth multiplierWidth row).ImplementsCycleContract
      (cycleContract multiplicandWidth multiplierWidth row)
      (Naming.ports multiplicandWidth multiplierWidth) :=
  Internal.construction_correct multiplicandWidth multiplierWidth row

theorem implements_contract (multiplicandWidth multiplierWidth : Nat)
    (row : Fin multiplierWidth) :
    Contracts.Cycle.Implements
      (moduleStructure multiplicandWidth multiplierWidth row)
      (cycleContract multiplicandWidth multiplierWidth row)
      (certification multiplicandWidth multiplierWidth row).stateCorresponds :=
  (certification multiplicandWidth multiplierWidth row).implements

/-- An allowed step has the exact natural-number partial-product value. -/
theorem result_toNat_of_allowed (multiplicandWidth multiplierWidth : Nat)
    (row : Fin multiplierWidth)
    {step : (cycleContract multiplicandWidth multiplierWidth row).Step}
    (allowed : (cycleContract multiplicandWidth multiplierWidth row).Allows step) :
    BitVector.toNat (multiplicandWidth + multiplierWidth)
        (step.outputs .result) =
      resultNat multiplicandWidth row
        (step.inputs .multiplicand) (step.inputs .select) := by
  rw [cycleContract.result multiplicandWidth multiplierWidth row allowed,
    Internal.toNat_resultValue]

end Silean.Modules.PartialProductRow
