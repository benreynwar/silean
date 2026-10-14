import Silean.Authoring.ModuleDesign
import Silean.Modules.PipelinedSignedMultiply.PipelinedSignedMultiply
import Silean.Modules.Register.RegisterDerived
import Silean.Modules.SignedMultiply.SignedMultiplyDerived

/-! Flat typed structure for the provisional output-registered multiplier. -/

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design PipelinedSignedMultiply (leftWidth : Nat) (rightWidth : Nat)
    (latency : Nat) where
  boundary (PipelinedSignedMultiply.ports leftWidth rightWidth)
    (naming := PipelinedSignedMultiply.Naming.ports leftWidth rightWidth)
  instances {
    product (name := .indexed "signed_multiply" 0) :=
      SignedMultiply.design leftWidth rightWidth,
    delay (stage : Fin latency in Enumeration.fin latency)
      (name := .indexed "register" stage.val) :=
        Register.design (.vector (leftWidth + rightWidth) .bit) }
  wiring {
    outputs {
      .result := from (
        if zero : latency = 0 then
          (PipelinedSignedMultiply.context leftWidth rightWidth latency)
            |>.instanceOutput .product .result
        else
          (PipelinedSignedMultiply.context leftWidth rightWidth latency)
            |>.instanceOutput (.delay ⟨latency - 1, by omega⟩) .output) }
    instance (.product) {
      .left := input.left,
      .right := input.right }
    instance (.delay stage) {
      .input := from (
        if first : stage.val = 0 then
          (PipelinedSignedMultiply.context leftWidth rightWidth latency)
            |>.instanceOutput .product .result
        else
          (PipelinedSignedMultiply.context leftWidth rightWidth latency)
            |>.instanceOutput (.delay ⟨stage.val - 1, by omega⟩) .output) }
  }

end Silean.Modules
