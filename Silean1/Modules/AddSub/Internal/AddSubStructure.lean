import Silean.Authoring.ModuleDesign
import Silean.Modules.AddSub.AddSub
import Silean.Modules.AddSubWithCarry.AddSubWithCarryDerived
import Silean.Modules.VectorLayout.Extensions
import Silean.Modules.VectorLayout.VectorLayoutDerived

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! Structural implementation of runtime-selectable fixed-width arithmetic. -/

module_design AddSub (leftWidth : Nat) (rightWidth : Nat)
    (leftSigned : Bool) (rightSigned : Bool) (extendOutput : Bool) where
  boundary
    (AddSub.ports leftWidth rightWidth leftSigned rightSigned extendOutput)
    (naming := AddSub.Naming.ports leftWidth rightWidth leftSigned rightSigned
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
    addSub (name := .indexed "add_sub_with_carry" 0) :=
      AddSubWithCarry.design
        (Arithmetic.resultWidth leftWidth rightWidth extendOutput) }
  wiring {
    outputs {
      .result := addSub.result }
    instance (.leftExtension) {
      .input := input.left }
    instance (.rightExtension) {
      .input := input.right }
    instance (.addSub) {
      .left := leftExtension.output,
      .right := rightExtension.output,
      .subtract := input.subtract }
  }

end Silean.Modules
