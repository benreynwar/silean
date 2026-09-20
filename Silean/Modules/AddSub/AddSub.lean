import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector
import Silean.Modules.Add.AddDerived

/-! # Fixed-width addition and subtraction

The contract defines addition and subtraction directly with carry and borrow.
The authored construction implements subtraction as `left + ~right + 1` using
the recursive adder.
-/

namespace Silean.Modules.AddSub

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring

module_ports ports (width : Nat) where
  input left : .vector width .bit,
  input right : .vector width .bit,
  input subtract : .bit,
  output result : .vector width .bit,
  output carryOut : .bit

def sumBit (left right carry : Bool) : Bool :=
  Primitives.xorValue (Primitives.xorValue left right) carry

def carryBit (left right carry : Bool) : Bool :=
  (left && right) || (left && carry) || (right && carry)

def borrowBit (left right borrow : Bool) : Bool :=
  (!left && (right || borrow)) || (right && borrow)

/-- Carry/borrow recursion underlying the independent arithmetic contract. -/
def operate : (width : Nat) → (Fin width → Bool) →
    (Fin width → Bool) → Bool → Bool → (Fin width → Bool) × Bool
  | 0, _, _, subtract, chain =>
      (fun index => Fin.elim0 index, if subtract then !chain else chain)
  | width + 1, left, right, subtract, chain =>
      let lower := operate width
        (fun index => left index.castSucc)
        (fun index => right index.castSucc) subtract chain
      let incoming := if subtract then !lower.2 else lower.2
      let high := sumBit (left (Fin.last width)) (right (Fin.last width)) incoming
      let outgoing := if subtract then
        borrowBit (left (Fin.last width)) (right (Fin.last width)) incoming
      else carryBit (left (Fin.last width)) (right (Fin.last width)) incoming
      (Fin.lastCases high lower.1, if subtract then !outgoing else outgoing)

/-- Natural addition or subtraction, initialized with no carry or borrow. -/
def addSubBits (width : Nat) (left right : Fin width → Bool) (subtract : Bool) :
    (Fin width → Bool) × Bool :=
  operate width left right subtract false

module_cycle_contract cycleContract (width : Nat) for ports width where
  state := emptySignalMap
  output_rule apply where
    reads := [left, right, subtract]
    writes := {
      result := (addSubBits width left right subtract).1,
      carryOut := (addSubBits width left right subtract).2 }
  state_rule where
    reads := []
    next := {}

/-- Broadcast shape used to present the subtraction bit to every operand bit. -/
def subtractVector (width : Nat) : Composition.SignalCombiner :=
  .vector width .bit

open ports

noncomputable def construction (width : Nat) : ModuleBuilder (ports width) Unit := do
  let left ← input width .left
  let right ← input width .right
  let subtract ← input width .subtract
  wire transformedRight ← right ^^^ (←
    combine (subtractVector width) fun _ => subtract)
  let added ← Add.place left transformedRight subtract
  output width .result added.result
  output width .carryOut added.carryOut

noncomputable def description (width : Nat) : Description :=
  ModuleBuilder.build (Naming.ports width) (construction width)

end Silean.Modules.AddSub
