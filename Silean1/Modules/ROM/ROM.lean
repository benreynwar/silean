import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Modules.CombMuxTree.CombMuxTree

/-! # Combinational read-only memory

A ROM contains exactly `2 ^ addressWidth` values and returns the value selected
by its binary address.  Its contents and emitted definition name are static
construction parameters; only the address is a hardware input.
-/

namespace Silean.Modules.ROM

open Silean
open Silean.Authoring

abbrev entryCount := BinaryToOneHot.size

module_ports ports (element : SignalType) (addressWidth : Nat)
    with (elementNaming : Silean.Naming.SignalTypeNaming element :=
      .positional element) where
  input address : .vector addressWidth .bit,
  output data (schema := elementNaming) : element

/-- Select the ROM entry denoted by the little-endian binary address. -/
def lookup (addressWidth : Nat)
    (contents : Fin (entryCount addressWidth) → α)
    (address : Fin addressWidth → Bool) : α :=
  contents (BitVector.toIndex addressWidth address)

module_cycle_contract cycleContract (element : SignalType) (addressWidth : Nat)
    (contents : Fin (entryCount addressWidth) → element.Denote)
    for ports element addressWidth where
  state := emptySignalMap
  output_rule read where
    reads := [address]
    writes := { data := lookup addressWidth contents address }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.ROM
