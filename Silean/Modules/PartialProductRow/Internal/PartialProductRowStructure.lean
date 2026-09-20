import Silean.Authoring.ModuleDesign
import Silean.Modules.Mask.Mask
import Silean.Modules.PartialProductRow.PartialProductRow
import Silean.Modules.VectorLayout.VectorLayoutDerived

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design PartialProductRow (multiplicandWidth : Nat) (multiplierWidth : Nat)
    (row : Fin multiplierWidth)
    (variant := s!"row_{row.val}")
    (specialization := [.natural multiplicandWidth, .natural multiplierWidth]) where
  boundary (PartialProductRow.ports multiplicandWidth multiplierWidth)
    (naming := PartialProductRow.Naming.ports
      multiplicandWidth multiplierWidth)
  instances {
    mask (name := .indexed "mask" 0) :=
      Mask.design (.vector multiplicandWidth .bit),
    shift (name := .indexed "left_shift" 0) :=
      VectorLayout.design multiplicandWidth
        (multiplicandWidth + multiplierWidth)
        (VectorLayout.wideningLeftShiftLayout
          multiplicandWidth multiplierWidth row.castSucc) }
  wiring {
    outputs {
      .result := shift.output }
    instance (.mask) {
      .value := input.multiplicand,
      .mask := input.select }
    instance (.shift) {
      .input := mask.result }
  }

end Silean.Modules
