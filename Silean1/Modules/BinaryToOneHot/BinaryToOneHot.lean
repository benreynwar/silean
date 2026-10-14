import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector

/-! # Binary-to-one-hot decoder

For a `width`-bit input, exactly one of the `2 ^ width` output bits is asserted.
The recursive hardware hierarchy lives under `Internal/`; this file contains
the boundary and its mathematical behavior.
-/

namespace Silean.Modules.BinaryToOneHot

open Silean
open Silean.Authoring

abbrev size := BitVector.cardinality

@[simp] theorem size_eq_pow (width : Nat) : size width = 2 ^ width :=
  BitVector.cardinality_eq_pow width

module_ports ports (width : Nat) where
  input value : .vector width .bit,
  output result : .vector (size width) .bit

/-- The asserted result position is the natural value of the input bits. -/
def oneHot (width : Nat) (bits : Fin width → Bool) :
    Fin (size width) → Bool :=
  fun index => decide (index.val = BitVector.toNat width bits)

module_cycle_contract cycleContract (width : Nat) for ports width where
  state := emptySignalMap
  output_rule apply where
    reads := [value]
    writes := { result := oneHot width value }
  state_rule where
    reads := []
    next := {}

/-- A result bit is asserted exactly at the decoded input index. -/
theorem result_eq_true_iff_of_allowed (width : Nat)
    {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step)
    (index : Fin (size width)) :
    step.outputs .result index = true ↔
      index.val = BitVector.toNat width (step.inputs .value) := by
  rw [cycleContract.result width allowed]
  exact decide_eq_true_iff

end Silean.Modules.BinaryToOneHot
