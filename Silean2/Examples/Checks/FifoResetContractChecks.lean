import Silean2.Modules.FifoResetContract

namespace Silean2.Examples.Checks.FifoResetContract

open Silean2
open Silean2.Modules.Fifo
open Silean2.Modules.Fifo.Reset

def inputs (valid data ready reset : Bool) :
    (Silean2.Modules.Fifo.ports .bit).inputs.Values
  | .inputValid => valid
  | .inputData => data
  | .outputReady => ready
  | .reset => reset

def outputs (valid data ready : Bool) :
    (Silean2.Modules.Fifo.ports .bit).outputs.Values
  | .outputValid => valid
  | .outputData => data
  | .inputReady => ready

example : inputReady 0 ([] : List Bool) = true := by simp
example : inputReady 0 [false] = false := by simp [inputReady, capacity]

example : nextQueue 1 true true false ([] : List Bool) = [true] := by rfl
example : nextQueue 1 false false true [true, false] = [false] := by rfl
example : nextQueue 1 true false true [true] = [false] := by rfl
example : nextQueue 1 false false false [true] = [true] := by rfl

example : (nextQueue 2 true true false [false, true]).length ≤ capacity 2 :=
  nextQueue_capacity 2 true true false [false, true] (by decide)

private theorem matchesEmpty (data : Bool) :
    (Silean2.Modules.Fifo.ports .bit).outputs.Matches
      (outputExpectations .bit 1 []) (outputs false data true) := by
  intro output
  cases output <;> change BitExpectation.Matches _ _ <;>
    simp [outputExpectations, outputs, inputReady, capacity,
      SignalType.dontCareExpectation, BitExpectation.exact,
      BitExpectation.Matches]

private theorem matchesOne :
    (Silean2.Modules.Fifo.ports .bit).outputs.Matches
      (outputExpectations .bit 1 [true]) (outputs true true true) := by
  intro output
  cases output <;> change BitExpectation.Matches _ _ <;>
    simp [outputExpectations, outputs, inputReady, capacity,
      SignalType.exactExpectation, BitExpectation.exact,
      BitExpectation.Matches]

theorem repeatedResetTrace : (contract .bit 1).TraceMatches none
    [inputs false false false true,
      inputs true true false false,
      inputs false false true false,
      inputs true false true true,
      inputs false false false false]
    [outputs true false false,
      outputs false true true,
      outputs true true true,
      outputs false false false,
      outputs false true true]
    (some []) := by
  refine Execution.Trace.cons _ _ (.reset rfl) ?_
  refine Execution.Trace.cons _ _ (.ordinary rfl (matchesEmpty true)) ?_
  refine Execution.Trace.cons _ _ (.ordinary rfl matchesOne) ?_
  refine Execution.Trace.cons _ _ (.reset rfl) ?_
  refine Execution.Trace.cons _ _ (.ordinary rfl (matchesEmpty true)) ?_
  exact .nil (some [])

example : SynchronizationBounded 1 (some ([] : List Bool)) :=
  TraceMatches.bounded_after_reset .bit 1 rfl repeatedResetTrace

example : (contract .bit 1).TraceMatches (some [])
    [inputs false false false false]
    [outputs false true true] (some []) := by
  apply trace_suffix_after_reset .bit 1 (prefixInputs :=
    [inputs false false false true, inputs true true false false,
      inputs false false true false])
    (prefixOutputs :=
      [outputs true false false, outputs false true true, outputs true true true])
    (resetInput := inputs true false true true)
    (resetOutput := outputs false false false)
  · rfl
  · rfl
  · exact repeatedResetTrace

end Silean2.Examples.Checks.FifoResetContract
