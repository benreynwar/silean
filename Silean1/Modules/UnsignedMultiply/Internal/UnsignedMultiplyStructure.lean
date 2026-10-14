import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.AddWithCarry.AddWithCarryDerived
import Silean.Modules.CarrySaveTree.CarrySaveTreeDerived
import Silean.Modules.Constant.Constant
import Silean.Modules.PartialProductRow.PartialProductRowDerived
import Silean.Modules.UnsignedMultiply.UnsignedMultiply
import Silean.Naming.SignalAdapterNaming

/-! Indexed structural implementation of full-width unsigned multiplication. -/

namespace Silean.Modules.UnsignedMultiply.Internal

open Silean

@[reducible] def rightSplitter (rightWidth : Nat) :
    Composition.SignalSplitter :=
  .vector rightWidth .bit

@[reducible] def rowCombiner (leftWidth rightWidth : Nat) :
    Composition.SignalCombiner :=
  .vector rightWidth (.vector (leftWidth + rightWidth) .bit)

end Silean.Modules.UnsignedMultiply.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design UnsignedMultiply (leftWidth : Nat) (rightWidth : Nat) where
  boundary (UnsignedMultiply.ports leftWidth rightWidth)
    (naming := UnsignedMultiply.Naming.ports leftWidth rightWidth)
  instances {
    rightSplit := Naming.SignalAdapter.splitterDesign
      (UnsignedMultiply.Internal.rightSplitter rightWidth),
    row (index : Fin rightWidth in Enumeration.fin rightWidth)
      (name := .indexed "partial_product_row" index.val) :=
        PartialProductRow.design leftWidth rightWidth index,
    rows := Naming.SignalAdapter.combinerDesign
      (UnsignedMultiply.Internal.rowCombiner leftWidth rightWidth),
    tree := CarrySaveTree.design (leftWidth + rightWidth) rightWidth,
    zero := Constant.design .bit false,
    add := AddWithCarry.design (leftWidth + rightWidth) }
  wiring {
    outputs {
      .result := add.result }
    instance (.rightSplit) {
      .value := input.right }
    instance (.row index) {
      .multiplicand := input.left,
      .select := rightSplit[index] }
    instance (.rows) {
      index := row(index)[.result] }
    instance (.tree) {
      .operands := rows.value }
    instance (.zero) {}
    instance (.add) {
      .left := tree.resultA,
      .right := tree.resultB,
      .carryIn := zero.output }
  }

end Silean.Modules
