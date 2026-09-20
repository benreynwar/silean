import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Modules.BinaryToOneHot.BinaryToOneHot

/-! # Combinational mux tree

This module selects one of `2 ^ indexWidth` values. Its recursive hierarchy is
internal; the public contract is ordinary indexed selection.
-/

namespace Silean.Modules.CombMuxTree

open Silean
open Silean.Authoring

module_ports ports (element : SignalType) (indexWidth : Nat)
    with (elementNaming : Silean.Naming.SignalTypeNaming element :=
      .positional element) where
  input values (schema := .vector elementNaming) :
    .vector (BinaryToOneHot.size indexWidth) element,
  input index : .vector indexWidth .bit,
  output result (schema := elementNaming) : element

def select (indexWidth : Nat)
    (values : Fin (BinaryToOneHot.size indexWidth) → α)
    (bits : Fin indexWidth → Bool) : α :=
  values (BitVector.toIndex indexWidth bits)

module_cycle_contract cycleContract (element : SignalType) (indexWidth : Nat)
    for ports element indexWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [values, index]
    writes := { result := select indexWidth values index }
  state_rule where
    reads := []
    next := {}

/-- The same selection law stated with the natural value of the index. -/
theorem result_at_index_of_allowed (element : SignalType) (indexWidth : Nat)
    {step : (cycleContract element indexWidth).Step}
    (allowed : (cycleContract element indexWidth).Allows step) :
    step.outputs .result = step.inputs .values
      ⟨BitVector.toNat indexWidth (step.inputs .index),
        BitVector.toNat_lt_cardinality indexWidth (step.inputs .index)⟩ := by
  rw [cycleContract.result element indexWidth allowed]
  unfold select
  apply congrArg (step.inputs .values)
  apply Fin.ext
  exact BitVector.toIndex_val indexWidth (step.inputs .index)

end Silean.Modules.CombMuxTree
