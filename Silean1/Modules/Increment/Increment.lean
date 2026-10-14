import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector
import Silean.Modules.HalfAdder.HalfAdder

/-! # Fixed-width increment

`Increment` adds one modulo the width of an LSB-first bit vector. The recursive
ripple implementation is kept under `Internal/`; this file contains only the
boundary and mathematical contract.
-/

namespace Silean.Modules.Increment

open Silean
open Silean.Authoring

module_ports ports (width : Nat) where
  input value : .vector width .bit,
  output result : .vector width .bit

/-- Add one carry bit to an LSB-first vector. Recursion computes the carry from
the lower indices before visiting the highest bit. -/
def addCarry : (width : Nat) → (Fin width → Bool) → Bool →
    (Fin width → Bool) × Bool
  | 0, _, carry => (fun index => Fin.elim0 index, carry)
  | width + 1, bits, carry =>
      let lower := addCarry width (fun index => bits index.castSucc) carry
      let high := HalfAdder.sumValue (bits (Fin.last width)) lower.2
      let carryOut := HalfAdder.carryValue (bits (Fin.last width)) lower.2
      (Fin.lastCases high lower.1, carryOut)

/-- Increment a bit vector, discarding carry beyond its fixed width. -/
def incrementValue (width : Nat) (bits : Fin width → Bool) : Fin width → Bool :=
  (addCarry width bits true).1

module_cycle_contract cycleContract (width : Nat) for ports width where
  state := emptySignalMap
  output_rule apply where
    reads := [value]
    writes := { result := incrementValue width value }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.Increment
