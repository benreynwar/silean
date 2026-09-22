import Silean.Modules.OptionalShiftRegister.OptionalShiftRegister
import Silean.Modules.ShiftRegister.ShiftRegister

assert_not_imported Silean.Modules.ShiftRegister.Internal.ShiftRegisterStructure
assert_not_imported Silean.Modules.ShiftRegister.Internal.ShiftRegisterVerification

namespace SileanTests.ShiftRegisterContractChecks

open Silean

example (signalType : SignalType) (latency : Nat) (positive : 0 < latency) :
    ((Modules.ShiftRegister.rules signalType latency positive).rule
      .output).reads = [] := rfl

example (signalType : SignalType) :
    ((Modules.OptionalShiftRegister.rules signalType 0).rule
      .output).reads = [.input] := rfl

example (signalType : SignalType) (latency : Nat) :
    ((Modules.OptionalShiftRegister.rules signalType (latency + 1)).rule
      .output).reads = [] := by simp

example (signalType : SignalType) (latency : Nat) (positive : 0 < latency)
    (trace : BoundaryTrace (Modules.ShiftRegister.ports signalType))
    (accepted : Modules.ShiftRegister.contract signalType latency positive
      trace)
    (t : Nat) (outputInTrace : t + latency < trace.length) :
    trace.outputs.get ⟨t + latency, by
      rw [BoundaryTrace.outputs_length]
      exact outputInTrace⟩ .output =
      trace.inputs.get ⟨t, by
        have inTrace : t < trace.length := by omega
        rw [BoundaryTrace.inputs_length]
        exact inTrace⟩ .input := by
  exact FixedLatency.boundary_relation_at accepted t outputInTrace

end SileanTests.ShiftRegisterContractChecks
