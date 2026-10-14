import Silean.Authoring.ModulePorts
import Silean.Semantics.FixedLatency
import Silean.Semantics.StructuralDependency

/-! # Positive-latency shift register

`ShiftRegister` delays an arbitrary signal by a statically selected positive
number of cycles.  Positivity is part of every public contract and placement
interface.  Consequently its output is always a value already held in state:
the output rule has no combinational dependency on the current input.
-/

namespace Silean.Modules.ShiftRegister

open Silean

module_ports ports (signalType : SignalType) where
  input input : signalType,
  output output : signalType

inductive Rule
  | output
deriving Enumeration

/-- Scheduling interface for a positive shift register.  The output depends
only on stored state, so its rule reads no current-cycle input. -/
@[reducible] def rules (signalType : SignalType) (latency : Nat)
    (_positive : 0 < latency) : ModuleStructuralRules (ports signalType) where
  RuleName := Rule
  ruleNames := inferInstance
  rule
    | .output => {
        reads := []
        writes := [.output] }
  outputCoverage := by rfl

/-- Natural trace-level behavior, independent of the register-chain
implementation. -/
def contract (signalType : SignalType) (latency : Nat)
    (_positive : 0 < latency)
    (trace : BoundaryTrace (ports signalType)) : Prop :=
  FixedLatency.Holds latency
    (fun (input : (ports signalType).inputs.Values)
        (output : (ports signalType).outputs.Values) =>
      output .output = input .input) trace

end Silean.Modules.ShiftRegister
