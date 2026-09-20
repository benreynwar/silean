import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector

/-! # Fixed-width addition

`Add` computes the wrapping result and carry-out of adding two equally wide
LSB-first vectors and a carry-in. Its recursive ripple implementation is kept
under `Internal/`; this file contains only the boundary and mathematical
contract.
-/

namespace Silean.Modules.Add

open Silean
open Silean.Authoring

module_ports ports (width : Nat) where
  input left : .vector width .bit,
  input right : .vector width .bit,
  input carryIn (name := "carry_in") : .bit,
  output result : .vector width .bit,
  output carryOut (name := "carry_out") : .bit

/-- Low bit of the natural sum of three Boolean digits. -/
def sumBit (left right carry : Bool) : Bool :=
  Primitives.xorValue (Primitives.xorValue left right) carry

/-- High bit of the natural sum of three Boolean digits. -/
def carryBit (left right carry : Bool) : Bool :=
  (left && right) || (left && carry) || (right && carry)

/-- Mathematical fixed-width binary addition on LSB-first vectors. -/
def addBits : (width : Nat) → (Fin width → Bool) →
    (Fin width → Bool) → Bool → (Fin width → Bool) × Bool
  | 0, _, _, carry => (fun index => Fin.elim0 index, carry)
  | width + 1, left, right, carry =>
      let lower := addBits width
        (fun index => left index.castSucc)
        (fun index => right index.castSucc) carry
      let high := sumBit
        (left (Fin.last width)) (right (Fin.last width)) lower.2
      let carryOut := carryBit
        (left (Fin.last width)) (right (Fin.last width)) lower.2
      (Fin.lastCases high lower.1, carryOut)

module_cycle_contract cycleContract (width : Nat) for ports width where
  state := emptySignalMap
  output_rule apply where
    reads := [left, right, carryIn]
    writes := {
      result := (addBits width left right carryIn).1,
      carryOut := (addBits width left right carryIn).2 }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.Add
