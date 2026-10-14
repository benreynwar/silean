import Silean.Authoring.ModulePorts
import Silean.Modules.BarrelShifter.BarrelShifter

/-! # One combinational barrel-shifter level

This is an implementation detail of `BarrelShifter`.  Level `stage` either
passes its vector unchanged or rotates it left by `2 ^ stage` positions,
according to the corresponding bit of the complete shift word.
-/

namespace Silean.Modules.BarrelShifter.Internal.Level

open Silean

/-- Input position selected by the static rotation at one mux level. -/
def sourceIndex (exponent : Nat) (stage : Fin exponent)
    (output : Fin (size exponent)) : Fin (size exponent) :=
  rotateSourceIndex exponent (2 ^ stage.val) output

/-- Static left rotation belonging to one mux level. -/
def rotatedValue (exponent : Nat) (stage : Fin exponent)
    (input : Fin (size exponent) → α) : Fin (size exponent) → α :=
  rotateValue exponent (2 ^ stage.val) input

/-- Natural Lean behavior of one conditional barrel-shifter level. -/
def resultValue (exponent : Nat) (stage : Fin exponent)
    (shift : Fin exponent → Bool)
    (input : Fin (size exponent) → α) : Fin (size exponent) → α :=
  bif shift stage then rotatedValue exponent stage input else input

module_ports ports (element : SignalType) (exponent : Nat) where
  input shift : .vector exponent .bit,
  input data : .vector (size exponent) element,
  output result : .vector (size exponent) element

end Silean.Modules.BarrelShifter.Internal.Level
