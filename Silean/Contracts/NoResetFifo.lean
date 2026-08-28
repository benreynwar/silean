namespace Silean.Contracts.NoResetFifo

structure Cycle (Word : Type) where
  enqValid : Bool
  enqData : Word
  enqReady : Bool
  deqValid : Bool
  deqData : Word
  deqReady : Bool

structure Trace (Word : Type) where
  initialContents : List Word
  cycles : List (Cycle Word)
  finalContents : List Word

def Cycle.acceptedInput (cycle : Cycle Word) : List Word :=
  bif cycle.enqValid && cycle.enqReady then [cycle.enqData] else []

def Cycle.acceptedOutput (cycle : Cycle Word) : List Word :=
  bif cycle.deqValid && cycle.deqReady then [cycle.deqData] else []

def acceptedInputs : List (Cycle Word) → List Word
  | [] => []
  | cycle :: cycles => cycle.acceptedInput ++ acceptedInputs cycles

def acceptedOutputs : List (Cycle Word) → List Word
  | [] => []
  | cycle :: cycles => cycle.acceptedOutput ++ acceptedOutputs cycles

def inputReadyStalls : List (Cycle Word) → Nat
  | [] => 0
  | cycle :: cycles =>
      (if cycle.enqReady then 0 else 1) + inputReadyStalls cycles

def outputReadyStalls : List (Cycle Word) → Nat
  | [] => 0
  | cycle :: cycles =>
      (if cycle.deqReady then 0 else 1) + outputReadyStalls cycles

structure Contract (capacity readyPropagationLatency : Nat)
    (trace : Trace Word) : Prop where
  conservation :
    trace.initialContents ++ acceptedInputs trace.cycles =
      acceptedOutputs trace.cycles ++ trace.finalContents
  capacity : trace.initialContents.length ≤ capacity →
    trace.finalContents.length ≤ capacity
  readyPropagation :
    inputReadyStalls trace.cycles ≤
      outputReadyStalls trace.cycles + readyPropagationLatency

namespace Contract

theorem outputs_prefix_inputs_of_empty
    {trace : Trace Word} {capacity readyPropagationLatency : Nat}
    (contract : Contract capacity readyPropagationLatency trace)
    (empty : trace.initialContents = []) :
    (acceptedOutputs trace.cycles).IsPrefix
      (acceptedInputs trace.cycles) := by
  apply List.prefix_iff_exists_append_eq.mpr
  refine ⟨trace.finalContents, ?_⟩
  have conserved := contract.conservation
  rw [empty, List.nil_append] at conserved
  exact conserved.symm

theorem accepted_count_conservation
    {trace : Trace Word} {capacity readyPropagationLatency : Nat}
    (contract : Contract capacity readyPropagationLatency trace) :
    trace.initialContents.length + (acceptedInputs trace.cycles).length =
      (acceptedOutputs trace.cycles).length + trace.finalContents.length := by
  have conserved := congrArg List.length contract.conservation
  simpa using conserved

end Contract

end Silean.Contracts.NoResetFifo
