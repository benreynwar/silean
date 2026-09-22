import Silean.Modules.PipelinedSignedMultiply.PipelinedSignedMultiply

assert_not_imported Silean.Modules.PipelinedSignedMultiply.Internal.PipelinedSignedMultiplyStructure
assert_not_imported Silean.Modules.PipelinedSignedMultiply.Internal.PipelinedSignedMultiplyVerification

namespace SileanTests.PipelinedSignedMultiplyContractChecks

open Silean
open Silean.Modules.PipelinedSignedMultiply

#check ports
#check contract

example (leftWidth rightWidth latency : Nat)
    (trace : BoundaryTrace (ports leftWidth rightWidth))
    (accepted : contract leftWidth rightWidth latency trace)
    (t : Nat) (outputInTrace : t + latency < trace.length) :
    (trace.outputs.get ⟨t + latency, by
      rw [BoundaryTrace.outputs_length]
      exact outputInTrace⟩) .result =
      Silean.Modules.SignedMultiply.resultValue leftWidth rightWidth
        ((trace.inputs.get ⟨t, by
          rw [BoundaryTrace.inputs_length]
          omega⟩) .left)
        ((trace.inputs.get ⟨t, by
          rw [BoundaryTrace.inputs_length]
          omega⟩) .right) := by
  exact FixedLatency.boundary_relation_at accepted t outputInTrace

end SileanTests.PipelinedSignedMultiplyContractChecks
