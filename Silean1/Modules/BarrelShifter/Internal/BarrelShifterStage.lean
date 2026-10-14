import Silean.Authoring.ModulePorts
import Silean.Modules.BarrelShifter.Internal.BarrelShifterLevel
import Silean.Semantics.FixedLatency

/-! # One optionally registered barrel-shifter stage

The stage delays the complete shift word and data vector by the same optional
cycle, then applies one combinational power-of-two rotation level.
-/

namespace Silean.Modules.BarrelShifter.Internal.Stage

open Silean

module_ports ports (element : SignalType) (exponent : Nat) where
  input shift : .vector exponent .bit,
  input data : .vector (size exponent) element,
  output shift (name := "shift_out") : .vector exponent .bit,
  output result : .vector (size exponent) element

/-- Natural fixed-latency behavior of one aligned pipeline stage. -/
def contract (element : SignalType) (exponent : Nat)
    (stage : Fin exponent) (registerInput : Bool)
    (trace : BoundaryTrace (ports element exponent)) : Prop :=
  FixedLatency.Holds registerInput.toNat
    (fun (input : (ports element exponent).inputs.Values)
        (output : (ports element exponent).outputs.Values) =>
      (output .shift, output .result) =
        (input .shift,
          Level.resultValue exponent stage (input .shift) (input .data))) trace

end Silean.Modules.BarrelShifter.Internal.Stage
