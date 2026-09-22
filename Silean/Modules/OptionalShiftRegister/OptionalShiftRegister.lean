import Silean.Modules.ShiftRegister.ShiftRegister

/-! # Zero-or-positive shift register

`OptionalShiftRegister` extends `ShiftRegister` with the useful zero-latency
case.  At zero latency it is a direct connection, so only that specialization's
output rule depends on the current input.
-/

namespace Silean.Modules.OptionalShiftRegister

open Silean

abbrev ports := ShiftRegister.ports

inductive Rule
  | output
deriving Enumeration

/-- Scheduling interface for a possibly empty register chain.  Only the
zero-latency specialization is combinationally dependent on the input. -/
@[reducible] def rules (signalType : SignalType) (latency : Nat) :
    ModuleStructuralRules (ports signalType) where
  RuleName := Rule
  ruleNames := inferInstance
  rule
    | .output => {
        reads := if latency = 0 then [.input] else []
        writes := [.output] }
  outputCoverage := by rfl

/-- Natural trace-level behavior for any statically selected latency. -/
def contract (signalType : SignalType) (latency : Nat)
    (trace : BoundaryTrace (ports signalType)) : Prop :=
  FixedLatency.Holds latency
    (fun (input : (ports signalType).inputs.Values)
        (output : (ports signalType).outputs.Values) =>
      output .output = input .input) trace

end Silean.Modules.OptionalShiftRegister
