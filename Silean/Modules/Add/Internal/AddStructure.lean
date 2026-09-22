import Silean.Authoring.ModuleDesign
import Silean.Modules.Add.Add
import Silean.Modules.AddWithCarry.AddWithCarryDerived
import Silean.Modules.Constant.Constant
import Silean.Modules.VectorLayout.Extensions
import Silean.Modules.VectorLayout.VectorLayoutDerived

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! Structural implementation of general fixed-width addition. -/

module_design Add (leftWidth : Nat) (rightWidth : Nat)
    (leftSigned : Bool) (rightSigned : Bool) (extendOutput : Bool) where
  boundary (Add.ports leftWidth rightWidth leftSigned rightSigned extendOutput)
    (naming := Add.Naming.ports leftWidth rightWidth leftSigned rightSigned
      extendOutput)
  instances {
    leftExtension (name := .indexed "vector_layout" 0) :=
      VectorLayout.design leftWidth
        (Arithmetic.resultWidth leftWidth rightWidth extendOutput)
        (VectorLayout.extensionLayout leftSigned leftWidth
          (Arithmetic.resultWidth leftWidth rightWidth extendOutput)),
    rightExtension (name := .indexed "vector_layout" 1) :=
      VectorLayout.design rightWidth
        (Arithmetic.resultWidth leftWidth rightWidth extendOutput)
        (VectorLayout.extensionLayout rightSigned rightWidth
          (Arithmetic.resultWidth leftWidth rightWidth extendOutput)),
    carryIn (name := .indexed "constant" 0) :=
      Constant.design .bit false,
    add (name := .indexed "add_with_carry" 0) :=
      AddWithCarry.design
        (Arithmetic.resultWidth leftWidth rightWidth extendOutput) }
  wiring {
    outputs {
      .result := add.result }
    instance (.leftExtension) {
      .input := input.left }
    instance (.rightExtension) {
      .input := input.right }
    instance (.carryIn) {}
    instance (.add) {
      .left := leftExtension.output,
      .right := rightExtension.output,
      .carryIn := carryIn.output }
  }

end Silean.Modules
