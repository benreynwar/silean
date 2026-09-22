import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Modules.Arithmetic

/-! # General fixed-width subtraction

`Sub` interprets independently sized inputs according to static signedness
parameters and subtracts the right value from the left.  Its output either
retains the wider input width or grows by one bit.  The contract is ordinary
integer subtraction followed by the explicit fixed-width encoding boundary.
-/

namespace Silean.Modules.Sub

open Silean
open Silean.Authoring

module_ports ports (leftWidth : Nat) (rightWidth : Nat)
    (leftSigned : Bool) (rightSigned : Bool) (extendOutput : Bool) where
  input left : .vector leftWidth .bit,
  input right : .vector rightWidth .bit,
  output result : .vector
    (Arithmetic.resultWidth leftWidth rightWidth extendOutput) .bit

/-- The encoded difference of the naturally interpreted operands. -/
def resultValue (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    Fin (Arithmetic.resultWidth leftWidth rightWidth extendOutput) → Bool :=
  Arithmetic.encode
    (Arithmetic.resultWidth leftWidth rightWidth extendOutput)
    (Arithmetic.operandValue leftSigned leftWidth left -
      Arithmetic.operandValue rightSigned rightWidth right)

module_cycle_contract cycleContract (leftWidth : Nat) (rightWidth : Nat)
    (leftSigned : Bool) (rightSigned : Bool) (extendOutput : Bool)
    for ports leftWidth rightWidth leftSigned rightSigned extendOutput where
  state := emptySignalMap
  output_rule apply where
    reads := [left, right]
    writes := {
      result := resultValue leftWidth rightWidth leftSigned rightSigned
        extendOutput left right }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.Sub
