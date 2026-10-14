import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector
import Silean.Modules.Mask.Mask
import Silean.Modules.VectorLayout.VectorLayoutDerived

/-! # Binary partial-product row

`PartialProductRow` masks a multiplicand with one multiplier bit and places the
result at a static offset in a full product-width vector.
-/

namespace Silean.Modules.PartialProductRow

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

module_ports ports (multiplicandWidth : Nat) (multiplierWidth : Nat) where
  input multiplicand : .vector multiplicandWidth .bit,
  input select : .bit,
  output result : .vector (multiplicandWidth + multiplierWidth) .bit

/-- Natural-number value of one ordinary binary partial-product row. -/
def resultNat (multiplicandWidth : Nat)
    (row : Fin multiplierWidth)
    (multiplicand : Fin multiplicandWidth → Bool) (select : Bool) : Nat :=
  if select then
    BitVector.toNat multiplicandWidth multiplicand <<< row.val
  else
    0

/-- Encode the mathematical partial product at the full product width. -/
def resultValue (multiplicandWidth multiplierWidth : Nat)
    (row : Fin multiplierWidth)
    (multiplicand : Fin multiplicandWidth → Bool) (select : Bool) :
    Fin (multiplicandWidth + multiplierWidth) → Bool :=
  BitVector.ofNat (multiplicandWidth + multiplierWidth)
    (resultNat multiplicandWidth row multiplicand select)

module_cycle_contract cycleContract (multiplicandWidth : Nat)
    (multiplierWidth : Nat)
    (row : Fin multiplierWidth)
    for ports multiplicandWidth multiplierWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [multiplicand, select]
    writes := {
      result := resultValue multiplicandWidth multiplierWidth row
        multiplicand select }
  state_rule where
    reads := []
    next := {}

open ports

noncomputable def construction (multiplicandWidth multiplierWidth : Nat)
    (row : Fin multiplierWidth) :
    ModuleBuilder (ports multiplicandWidth multiplierWidth) Unit := do
  let multiplicand ← input multiplicandWidth multiplierWidth .multiplicand
  let select ← input multiplicandWidth multiplierWidth .select
  output multiplicandWidth multiplierWidth .result
    (← VectorLayout.placeWideningLeftShift multiplierWidth row.castSucc
      (← Mask.place multiplicand select))

noncomputable def description (multiplicandWidth multiplierWidth : Nat)
    (row : Fin multiplierWidth) : Description :=
  ModuleBuilder.build (Naming.ports multiplicandWidth multiplierWidth)
    (construction multiplicandWidth multiplierWidth row)

end Silean.Modules.PartialProductRow
