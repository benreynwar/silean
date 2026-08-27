import Silean2.Modules.FifoResetCertified

namespace Silean2.Examples.Checks.FifoResetCertified

open Silean2
open Silean2.Modules

def inputs (valid data ready reset : Bool) :
    (Fifo.ports .bit).inputs.Values
  | .inputValid => valid
  | .inputData => data
  | .outputReady => ready
  | .reset => reset

example (initialState : (Fifo.moduleStructure .bit 1).State)
    (traceInputs : List (Fifo.ports .bit).inputs.Values) :
    ∃ outputs finalState,
      (Fifo.moduleStructure .bit 1).Executes initialState traceInputs outputs
          finalState ∧
        (Fifo.resetContract .bit 1).Accepts traceInputs outputs := by
  exact (Fifo.resetCertified .bit 1).accepted_execution_exists
    initialState traceInputs

example {initialState finalState : (Fifo.moduleStructure .bit 1).State}
    {resetOutput : (Fifo.ports .bit).outputs.Values}
    {traceInputs : List (Fifo.ports .bit).inputs.Values}
    {traceOutputs : List (Fifo.ports .bit).outputs.Values}
    (execution : (Fifo.moduleStructure .bit 1).Executes initialState
      (inputs false false false true :: traceInputs)
      (resetOutput :: traceOutputs) finalState) :
    ∃ finalSynchronization,
      (Fifo.resetContract .bit 1).TraceMatches (some [])
        traceInputs traceOutputs finalSynchronization :=
  (Fifo.resetCertified .bit 1).matches_after_initial_reset rfl execution

/-! The prefix is arbitrary and may contain an earlier reset. A later reset
starts a fresh empty-queue comparison. -/
example {initialState finalState : (Fifo.moduleStructure .bit 1).State}
    {prefixInputs : List (Fifo.ports .bit).inputs.Values}
    {prefixOutputs : List (Fifo.ports .bit).outputs.Values}
    {resetOutput : (Fifo.ports .bit).outputs.Values}
    {traceInputs : List (Fifo.ports .bit).inputs.Values}
    {traceOutputs : List (Fifo.ports .bit).outputs.Values}
    (lengths : prefixOutputs.length = prefixInputs.length)
    (execution : (Fifo.moduleStructure .bit 1).Executes initialState
      (prefixInputs ++ inputs true false true true :: traceInputs)
      (prefixOutputs ++ resetOutput :: traceOutputs) finalState) :
    ∃ finalSynchronization,
      (Fifo.resetContract .bit 1).TraceMatches (some [])
        traceInputs traceOutputs finalSynchronization :=
  (Fifo.resetCertified .bit 1).matches_after_reset lengths rfl execution

end Silean2.Examples.Checks.FifoResetCertified
