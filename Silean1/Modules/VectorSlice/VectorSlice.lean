import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

/-! # Vector slice

`VectorSlice` extracts a contiguous range after `prefixWidth` elements and
before `suffixWidth` elements.
-/

namespace Silean.Modules.VectorSlice

open Silean
open Silean.Authoring

module_ports ports (element : SignalType) (prefixWidth : Nat)
    (width : Nat) (suffixWidth : Nat)
    with (elementNaming : Naming.SignalTypeNaming element :=
      .positional element) where
  input value (schema := .vector elementNaming) :
    .vector (prefixWidth + width + suffixWidth) element,
  output result (schema := .vector elementNaming) : .vector width element

def slice (value : Fin (prefixWidth + width + suffixWidth) → α) : Fin width → α :=
  fun index => value (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index))

module_cycle_contract cycleContract (element : SignalType)
    (prefixWidth : Nat) (width : Nat) (suffixWidth : Nat)
    for ports element prefixWidth width suffixWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [value]
    writes := { result := slice value }
  state_rule where
    reads := []
    next := {}

theorem result_at_of_allowed (element : SignalType)
    (prefixWidth width suffixWidth : Nat)
    {step : (cycleContract element prefixWidth width suffixWidth).Step}
    (allowed : (cycleContract element prefixWidth width suffixWidth).Allows step)
    (index : Fin width) :
    step.outputs .result index =
      step.inputs .value
        (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index)) := by
  rw [cycleContract.result element prefixWidth width suffixWidth allowed]
  rfl

end Silean.Modules.VectorSlice
