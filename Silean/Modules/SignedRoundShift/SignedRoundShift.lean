import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector

/-! # Signed rounded right shift

`SignedRoundShift` removes a statically known number of low bits from a
two's-complement value and rounds the retained signed value to nearest, with
ties to even. This file contains only the public boundary and natural Lean
contract; the hardware structure is deliberately separate.
-/

namespace Silean.Modules.SignedRoundShift

open Silean
open Silean.Authoring

module_ports ports (retainedWidth : Nat) (discardedWidth : Nat) where
  input value : .vector (discardedWidth + retainedWidth) .bit,
  output result : .vector retainedWidth .bit

/-- Divide a signed integer by `2 ^ discardedWidth`, rounding to nearest and
sending an exact half to the even integer. -/
def roundNearestEven (discardedWidth : Nat) (value : Int) : Int :=
  let divisor : Int := 2 ^ discardedWidth
  let lower := value / divisor
  let remainder := value % divisor
  let comparison := 2 * remainder
  if comparison < divisor then
    lower
  else if divisor < comparison then
    lower + 1
  else if lower % 2 = 0 then
    lower
  else
    lower + 1

/-- The destination-width encoding of the rounded signed value. -/
def resultValue (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    Fin retainedWidth → Bool :=
  BitVector.ofBitVec <| BitVec.ofInt retainedWidth <|
    roundNearestEven discardedWidth
      (BitVector.toBitVec (discardedWidth + retainedWidth) value).toInt

module_cycle_contract cycleContract (retainedWidth : Nat) (discardedWidth : Nat)
    for ports retainedWidth discardedWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [value]
    writes := {
      result := resultValue retainedWidth discardedWidth value }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.SignedRoundShift
