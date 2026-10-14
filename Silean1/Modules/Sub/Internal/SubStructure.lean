import Silean.Authoring.ModuleDesign
import Silean.Modules.AddSubWithCarry.AddSubWithCarryDerived
import Silean.Modules.Constant.Constant
import Silean.Modules.Sub.Sub
import Silean.Modules.VectorLayout.Extensions
import Silean.Modules.VectorLayout.VectorLayoutDerived

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! Structural implementation of general fixed-width subtraction. -/

module_design Sub (leftWidth : Nat) (rightWidth : Nat)
    (leftSigned : Bool) (rightSigned : Bool) (extendOutput : Bool) where
  boundary (Sub.ports leftWidth rightWidth leftSigned rightSigned extendOutput)
    (naming := Sub.Naming.ports leftWidth rightWidth leftSigned rightSigned
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
    subtract (name := .indexed "constant" 0) :=
      Constant.design .bit true,
    sub (name := .indexed "add_sub_with_carry" 0) :=
      AddSubWithCarry.design
        (Arithmetic.resultWidth leftWidth rightWidth extendOutput) }
  wiring {
    outputs {
      .result := sub.result }
    instance (.leftExtension) {
      .input := input.left }
    instance (.rightExtension) {
      .input := input.right }
    instance (.subtract) {}
    instance (.sub) {
      .left := leftExtension.output,
      .right := rightExtension.output,
      .subtract := subtract.output }
  }

end Silean.Modules
