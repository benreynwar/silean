import Silean.Authoring.ModuleDesign
import Silean.Modules.CombMuxTree.CombMuxTreeDerived
import Silean.Modules.Constant.Constant
import Silean.Modules.ROM.ROM

/-! Expanded constant-table and mux-tree implementation of a ROM. -/

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design ROM (definitionName : String) (element : SignalType)
    (addressWidth : Nat)
    (contents : Fin (ROM.entryCount addressWidth) → element.Denote)
    (name := "ROM")
    (variant := definitionName)
    (specialization := [.signalType element, .natural addressWidth])
    with (elementNaming : Naming.SignalTypeNaming element :=
      .positional element) where
  boundary (ROM.ports element addressWidth)
    (naming := ROM.Naming.ports element addressWidth)
    (namingWith := ROM.Naming.portsWithNaming
      element addressWidth elementNaming)
  instances {
    contents
      (naming := Constant.Naming.namingWith
        (.vector (ROM.entryCount addressWidth) element) contents
        (.vector elementNaming)) := Constant.design
      (.vector (ROM.entryCount addressWidth) element) contents,
    select
      (naming := CombMuxTree.Naming.namingWith
        element addressWidth elementNaming) :=
      CombMuxTree.design element addressWidth }
  wiring {
    outputs {
      .data := select.result }
    instance (.contents) {}
    instance (.select) {
      .values := contents.output,
      .index := input.address }
  }

end Silean.Modules
