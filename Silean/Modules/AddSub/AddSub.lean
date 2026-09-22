import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Modules.Arithmetic

/-! # General selectable fixed-width addition and subtraction

`AddSub` shares the same static width and operand-interpretation policy as
`Add` and `Sub`, while choosing the operation from a runtime input.  `false`
selects addition and `true` selects left-minus-right subtraction.
-/

namespace Silean.Modules.AddSub

open Silean
open Silean.Authoring

module_ports ports (leftWidth : Nat) (rightWidth : Nat)
    (leftSigned : Bool) (rightSigned : Bool) (extendOutput : Bool) where
  input left : .vector leftWidth .bit,
  input right : .vector rightWidth .bit,
  input subtract : .bit,
  output result : .vector
    (Arithmetic.resultWidth leftWidth rightWidth extendOutput) .bit

/-- The encoded result selected from ordinary integer addition or
subtraction. -/
def resultValue (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool)
    (subtract : Bool) :
    Fin (Arithmetic.resultWidth leftWidth rightWidth extendOutput) → Bool :=
  let leftValue := Arithmetic.operandValue leftSigned leftWidth left
  let rightValue := Arithmetic.operandValue rightSigned rightWidth right
  Arithmetic.encode
    (Arithmetic.resultWidth leftWidth rightWidth extendOutput)
    (if subtract then leftValue - rightValue else leftValue + rightValue)

module_cycle_contract cycleContract (leftWidth : Nat) (rightWidth : Nat)
    (leftSigned : Bool) (rightSigned : Bool) (extendOutput : Bool)
    for ports leftWidth rightWidth leftSigned rightSigned extendOutput where
  state := emptySignalMap
  output_rule apply where
    reads := [left, right, subtract]
    writes := {
      result := resultValue leftWidth rightWidth leftSigned rightSigned
        extendOutput left right subtract }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.AddSub
