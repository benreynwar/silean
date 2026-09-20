import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

/-! # Vector reindexing

`VectorReindex` constructs a vector by selecting an input element for every
output position. It is generic over the element signal type and represents
only wiring: elements may be permuted, duplicated, or omitted.
-/

namespace Silean.Modules.VectorReindex

open Silean
open Silean.Authoring

/-- Apply a static vector reindexing in ordinary Lean. -/
def apply (layout : Fin outputWidth → Fin inputWidth)
    (input : Fin inputWidth → α) : Fin outputWidth → α :=
  fun index => input (layout index)

@[simp] theorem apply_at (layout : Fin outputWidth → Fin inputWidth)
    (input : Fin inputWidth → α) (index : Fin outputWidth) :
    apply layout input index = input (layout index) := rfl

module_ports ports (element : SignalType) (inputWidth : Nat) (outputWidth : Nat)
    with (elementNaming : Naming.SignalTypeNaming element :=
      .positional element) where
  input input (schema := .vector elementNaming) : .vector inputWidth element,
  output output (schema := .vector elementNaming) : .vector outputWidth element

module_cycle_contract cycleContract (element : SignalType)
    (inputWidth : Nat) (outputWidth : Nat)
    (layout : Fin outputWidth → Fin inputWidth)
    for ports element inputWidth outputWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [input]
    writes := { output := VectorReindex.apply layout input }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.VectorReindex
