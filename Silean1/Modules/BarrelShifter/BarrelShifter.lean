import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector
import Silean.Semantics.FixedLatency

/-! # Pipelined barrel shifter

`BarrelShifter` rotates a power-of-two vector left by the unsigned amount on
its shift input.  Its public meaning is an ordinary finite-vector rotation;
the logarithmic mux network and its optional pipeline registers belong to the
structural implementation.
-/

namespace Silean.Modules.BarrelShifter

open Silean

/-- Number of elements in a barrel shifter with the given shift width. -/
abbrev size (exponent : Nat) : Nat := 2 ^ exponent

/-- Optional registers at the input, between mux levels, and at the output.
Boundary zero precedes the first mux level and boundary `exponent` follows the
last one. -/
structure Pipeline (exponent : Nat) where
  registerBoundary : Fin (exponent + 1) → Bool

/-- Number of cycles contributed by the selected optional registers. -/
def Pipeline.latency (pipeline : Pipeline exponent) : Nat :=
  ((List.finRange (exponent + 1)).map fun boundary =>
    (pipeline.registerBoundary boundary).toNat).sum

/-- Input position selected for one output position by an arbitrary natural
left-rotation amount. -/
def rotateSourceIndex (exponent amount : Nat)
    (output : Fin (size exponent)) : Fin (size exponent) :=
  ⟨(output.val + amount) % size exponent, by
    exact Nat.mod_lt _ (Nat.two_pow_pos exponent)⟩

/-- Rotate a power-of-two vector left by an arbitrary natural amount. -/
def rotateValue (exponent amount : Nat)
    (input : Fin (size exponent) → α) : Fin (size exponent) → α :=
  fun output => input (rotateSourceIndex exponent amount output)

/-- Input position selected for one output position by the encoded shift. -/
def sourceIndex (exponent : Nat) (shift : Fin exponent → Bool)
    (output : Fin (size exponent)) : Fin (size exponent) :=
  rotateSourceIndex exponent (BitVector.toNat exponent shift) output

/-- Natural Lean meaning of the barrel shifter.  Output position `i` receives
input position `i + shift`, modulo the vector size. -/
def resultValue (exponent : Nat) (shift : Fin exponent → Bool)
    (input : Fin (size exponent) → α) : Fin (size exponent) → α :=
  rotateValue exponent (BitVector.toNat exponent shift) input

@[simp] theorem resultValue_at (exponent : Nat)
    (shift : Fin exponent → Bool) (input : Fin (size exponent) → α)
    (output : Fin (size exponent)) :
    resultValue exponent shift input output =
      input (sourceIndex exponent shift output) :=
  rfl

module_ports ports (element : SignalType) (exponent : Nat) where
  input shift : .vector exponent .bit,
  input data : .vector (size exponent) element,
  output result : .vector (size exponent) element

/-- A selected vector rotation appears after the statically selected pipeline
latency. -/
def contract (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent)
    (trace : BoundaryTrace (ports element exponent)) : Prop :=
  FixedLatency.Holds pipeline.latency
    (fun (input : (ports element exponent).inputs.Values)
        (output : (ports element exponent).outputs.Values) =>
      output .result =
        resultValue exponent (input .shift) (input .data)) trace

end Silean.Modules.BarrelShifter
