import Silean.Interfaces.ValidReady
import Silean.Semantics.Trace
import Silean.Semantics.StructuralExecution

namespace Silean.Contracts.Fifo

/-! # Latency-independent FIFO contracts

A `FifoContract` observes only valid/ready payload transfers and synchronous
reset. After reset it requires the sequence leaving the source interface to be
the sequence accepted at the sink interface, in order and within the declared
capacity. It permits both combinational fall-through and registered latency.

The contract does not expose a cycle state or require any mapping to structural
state. Its synchronization state is only the abstract queue reconstructed from
the observed trace; behavior before the first reset is unconstrained. -/

structure FifoContract (ports : ModulePorts) (payloadTypes : SignalTypes) where
  /-- Valid/ready boundary through which values enter the FIFO. -/
  sink : Interfaces.ValidReadySink ports payloadTypes
  /-- Valid/ready boundary through which values leave the FIFO. -/
  source : Interfaces.ValidReadySource ports payloadTypes
  /-- Synchronous reset input. -/
  reset : ports.inputs.Label
  /-- Evidence that the reset input is one bit. -/
  resetType : ports.inputs.signalType reset = .bit
  /-- Maximum number of queued payloads. -/
  capacity : Nat

namespace FifoContract

abbrev Payload (_contract : FifoContract ports payloadTypes) := payloadTypes.Denote
abbrev Queue (contract : FifoContract ports payloadTypes) := List contract.Payload
abbrev BoundedQueue (contract : FifoContract ports payloadTypes) :=
  { queue : contract.Queue // queue.length ≤ contract.capacity }
abbrev Synchronization (contract : FifoContract ports payloadTypes) :=
  Option contract.BoundedQueue

def emptyQueue (contract : FifoContract ports payloadTypes) :
    contract.BoundedQueue :=
  ⟨[], Nat.zero_le _⟩

def resetSynchronization (contract : FifoContract ports payloadTypes) :
    contract.Synchronization :=
  some contract.emptyQueue

def resetAsserted (contract : FifoContract ports payloadTypes)
    (inputs : ports.inputs.Values) : Bool :=
  cast (congrArg SignalType.Denote contract.resetType) (inputs contract.reset)

def inputTransfer (contract : FifoContract ports payloadTypes)
    (inputs : ports.inputs.Values) (outputs : ports.outputs.Values) :
    List contract.Payload :=
  match (contract.sink.sample inputs outputs).transferredPayload? with
  | some payload => [payload]
  | none => []

def outputTransfer (contract : FifoContract ports payloadTypes)
    (inputs : ports.inputs.Values) (outputs : ports.outputs.Values) :
    List contract.Payload :=
  match (contract.source.sample inputs outputs).transferredPayload? with
  | some payload => [payload]
  | none => []

/-! Before the first reset behavior is unconstrained. Reset starts an empty
queue after the reset edge. The ordinary-cycle equation permits either
fall-through or registered latency. -/
inductive CycleMatches (contract : FifoContract ports payloadTypes) :
    ports.inputs.Values → contract.Synchronization → ports.outputs.Values →
      contract.Synchronization → Prop
  | reset {inputs synchronization outputs}
      (asserted : contract.resetAsserted inputs = true) :
      CycleMatches contract inputs synchronization outputs contract.resetSynchronization
  | beforeReset {inputs outputs}
      (ordinary : contract.resetAsserted inputs = false) :
      CycleMatches contract inputs none outputs none
  | ordinary {inputs outputs queue nextQueue}
      (notReset : contract.resetAsserted inputs = false)
      (preserves : queue.1 ++ contract.inputTransfer inputs outputs =
        contract.outputTransfer inputs outputs ++ nextQueue.1) :
      CycleMatches contract inputs (some queue) outputs (some nextQueue)

/-- The synchronized, reset-free part of a FIFO trace. -/
def OrdinaryCycleMatches (contract : FifoContract ports payloadTypes)
    (inputs : ports.inputs.Values) (queue : contract.BoundedQueue)
    (outputs : ports.outputs.Values) (nextQueue : contract.BoundedQueue) : Prop :=
  contract.resetAsserted inputs = false ∧
    queue.1 ++ contract.inputTransfer inputs outputs =
      contract.outputTransfer inputs outputs ++ nextQueue.1

abbrev OrdinaryTraceMatches (contract : FifoContract ports payloadTypes) :=
  Trace contract.OrdinaryCycleMatches

abbrev TraceMatches (contract : FifoContract ports payloadTypes) :=
  Trace contract.CycleMatches

def Accepts (contract : FifoContract ports payloadTypes)
    (inputs : List ports.inputs.Values) (outputs : List ports.outputs.Values) : Prop :=
  ∃ finalSynchronization,
    contract.TraceMatches none inputs outputs finalSynchronization

def transferredInputs (contract : FifoContract ports payloadTypes) :
    List ports.inputs.Values → List ports.outputs.Values → List contract.Payload
  | input :: inputs, output :: outputs =>
      contract.inputTransfer input output ++ contract.transferredInputs inputs outputs
  | _, _ => []

def transferredOutputs (contract : FifoContract ports payloadTypes) :
    List ports.inputs.Values → List ports.outputs.Values → List contract.Payload
  | input :: inputs, output :: outputs =>
      contract.outputTransfer input output ++ contract.transferredOutputs inputs outputs
  | _, _ => []

@[simp] theorem CycleMatches.reset_iff
    (contract : FifoContract ports payloadTypes)
    {inputs : ports.inputs.Values} {outputs : ports.outputs.Values}
    {initial final : contract.Synchronization}
    (asserted : contract.resetAsserted inputs = true) :
    contract.CycleMatches inputs initial outputs final ↔
      final = contract.resetSynchronization := by
  constructor
  · intro cycle
    cases cycle with
    | reset => rfl
    | beforeReset ordinary => simp [asserted] at ordinary
    | ordinary notReset _ => simp [asserted] at notReset
  · intro equal
    cases equal
    exact .reset asserted

@[simp] theorem CycleMatches.beforeReset_iff
    (contract : FifoContract ports payloadTypes)
    {inputs : ports.inputs.Values} {outputs : ports.outputs.Values}
    {final : contract.Synchronization}
    (notReset : contract.resetAsserted inputs = false) :
    contract.CycleMatches inputs none outputs final ↔ final = none := by
  constructor
  · intro cycle
    cases cycle with
    | reset asserted => simp [notReset] at asserted
    | beforeReset => rfl
  · intro equal
    cases equal
    exact .beforeReset notReset

theorem TraceMatches.append
    {contract : FifoContract ports payloadTypes}
    {initial middle final : contract.Synchronization}
    {leftInputs rightInputs : List ports.inputs.Values}
    {leftOutputs rightOutputs : List ports.outputs.Values}
    (left : contract.TraceMatches initial leftInputs leftOutputs middle)
    (right : contract.TraceMatches middle rightInputs rightOutputs final) :
    contract.TraceMatches initial (leftInputs ++ rightInputs)
      (leftOutputs ++ rightOutputs) final :=
  Trace.append left right

theorem TraceMatches.split
    {contract : FifoContract ports payloadTypes}
    {initial final : contract.Synchronization}
    {leftInputs rightInputs : List ports.inputs.Values}
    {leftOutputs rightOutputs : List ports.outputs.Values}
    (trace : contract.TraceMatches initial (leftInputs ++ rightInputs)
      (leftOutputs ++ rightOutputs) final)
    (lengths : leftOutputs.length = leftInputs.length) :
    ∃ middle, contract.TraceMatches initial leftInputs leftOutputs middle ∧
      contract.TraceMatches middle rightInputs rightOutputs final :=
  Trace.split trace lengths

theorem TraceMatches.after_reset
    {contract : FifoContract ports payloadTypes}
    {initial final : contract.Synchronization}
    {resetInput : ports.inputs.Values} {inputs : List ports.inputs.Values}
    {resetOutput : ports.outputs.Values} {outputs : List ports.outputs.Values}
    (asserted : contract.resetAsserted resetInput = true)
    (trace : contract.TraceMatches initial (resetInput :: inputs)
      (resetOutput :: outputs) final) :
    contract.TraceMatches contract.resetSynchronization inputs outputs final := by
  cases trace with
  | cons _ _ first rest =>
      have equal := (CycleMatches.reset_iff contract asserted).mp first
      cases equal
      exact rest

/-- A synchronized trace containing no reset cycles is exactly an ordinary
FIFO trace, and therefore ends in a bounded logical queue. -/
theorem TraceMatches.toOrdinary
    {contract : FifoContract ports payloadTypes}
    {initial : contract.BoundedQueue} {final : contract.Synchronization}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (trace : contract.TraceMatches (some initial) inputs outputs final)
    (notReset : ∀ input, input ∈ inputs →
      contract.resetAsserted input = false) :
    ∃ finalQueue, final = some finalQueue ∧
      contract.OrdinaryTraceMatches initial inputs outputs finalQueue := by
  generalize synchronizationEq : (some initial : contract.Synchronization) =
    synchronization at trace
  induction trace generalizing initial with
  | nil =>
      cases synchronizationEq
      exact ⟨initial, rfl, .nil initial⟩
  | cons input output cycle rest induction =>
      cases synchronizationEq
      have inputNotReset := notReset input (by simp)
      cases cycle with
      | reset asserted => simp [inputNotReset] at asserted
      | ordinary ordinaryReset preserves =>
          rcases induction (fun tailInput member =>
            notReset tailInput (List.mem_cons_of_mem input member)) rfl with
            ⟨finalQueue, finalEq, ordinaryRest⟩
          exact ⟨finalQueue, finalEq,
            .cons input output ⟨ordinaryReset, preserves⟩ ordinaryRest⟩

/-- Remove a reset cycle and expose a following reset-free suffix as an
ordinary trace starting from the empty queue. -/
theorem TraceMatches.after_reset_toOrdinary
    {contract : FifoContract ports payloadTypes}
    {initial final : contract.Synchronization}
    {resetInput : ports.inputs.Values} {inputs : List ports.inputs.Values}
    {resetOutput : ports.outputs.Values} {outputs : List ports.outputs.Values}
    (asserted : contract.resetAsserted resetInput = true)
    (notReset : ∀ input, input ∈ inputs →
      contract.resetAsserted input = false)
    (trace : contract.TraceMatches initial (resetInput :: inputs)
      (resetOutput :: outputs) final) :
    ∃ finalQueue, final = some finalQueue ∧
      contract.OrdinaryTraceMatches contract.emptyQueue inputs outputs finalQueue := by
  have suffix := TraceMatches.after_reset asserted trace
  exact TraceMatches.toOrdinary suffix notReset

theorem OrdinaryTraceMatches.transfer_equation
    {contract : FifoContract ports payloadTypes}
    {initial final : contract.BoundedQueue}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (trace : contract.OrdinaryTraceMatches initial inputs outputs final) :
    initial.1 ++ contract.transferredInputs inputs outputs =
      contract.transferredOutputs inputs outputs ++ final.1 := by
  induction trace with
  | nil => simp [transferredInputs, transferredOutputs]
  | cons input output cycle rest induction =>
      simp only [transferredInputs, transferredOutputs]
      rw [← List.append_assoc, cycle.2, List.append_assoc, induction]
      simp [List.append_assoc]

theorem OrdinaryTraceMatches.outputs_prefix_inputs
    {contract : FifoContract ports payloadTypes}
    {final : contract.BoundedQueue}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (trace : contract.OrdinaryTraceMatches contract.emptyQueue
      inputs outputs final) :
    (contract.transferredOutputs inputs outputs).IsPrefix
      (contract.transferredInputs inputs outputs) := by
  apply List.prefix_iff_exists_append_eq.mpr
  refine ⟨final.1, ?_⟩
  simpa [emptyQueue] using (OrdinaryTraceMatches.transfer_equation trace).symm

theorem OrdinaryTraceMatches.transfers_equal_when_drained
    {contract : FifoContract ports payloadTypes}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (trace : contract.OrdinaryTraceMatches contract.emptyQueue
      inputs outputs contract.emptyQueue) :
    contract.transferredInputs inputs outputs =
      contract.transferredOutputs inputs outputs := by
  simpa [emptyQueue] using OrdinaryTraceMatches.transfer_equation trace

theorem BoundedQueue.capacity_bound
    {contract : FifoContract ports payloadTypes}
    (queue : contract.BoundedQueue) : queue.1.length ≤ contract.capacity :=
  queue.2

end FifoContract

def ImplementsFifoContract (moduleStructure : ModuleStructure ports)
    (contract : FifoContract ports payloadTypes) : Prop :=
  ∀ initialState inputs outputs finalState,
    moduleStructure.Executes initialState inputs outputs finalState →
      contract.Accepts inputs outputs

/-! `hasSolution` makes certification non-vacuous: an inconsistent structure
cannot satisfy the trace refinement merely because it has no executions. -/
structure FifoCertified (ports : ModulePorts) (payloadTypes : SignalTypes) where
  /-- The hardware hierarchy. -/
  moduleStructure : ModuleStructure ports
  /-- Its latency-independent FIFO behavior. -/
  contract : FifoContract ports payloadTypes
  /-- Structural execution exists for every input trace. -/
  hasSolution : moduleStructure.HasSolution
  /-- Every structural trace preserves FIFO ordering and capacity after reset. -/
  implements : ImplementsFifoContract moduleStructure contract

namespace FifoCertified

theorem transition_exists (certified : FifoCertified ports payloadTypes)
    (inputs : ports.inputs.Values)
    (currentState : certified.moduleStructure.State) :
    ∃ outputs nextState,
      certified.moduleStructure.Transition inputs currentState outputs nextState :=
  certified.hasSolution.transition_exists inputs currentState

theorem execution_exists (certified : FifoCertified ports payloadTypes)
    (initialState : certified.moduleStructure.State)
    (inputs : List ports.inputs.Values) :
    ∃ outputs finalState,
      certified.moduleStructure.Executes initialState inputs outputs finalState :=
  certified.hasSolution.execution_exists initialState inputs

theorem accepts_execution (certified : FifoCertified ports payloadTypes)
    {initialState finalState : certified.moduleStructure.State}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (execution : certified.moduleStructure.Executes initialState inputs outputs finalState) :
    certified.contract.Accepts inputs outputs :=
  certified.implements initialState inputs outputs finalState execution

/-- Every input trace has a real structural execution, and that execution is
accepted by the FIFO contract. -/
theorem accepted_execution_exists (certified : FifoCertified ports payloadTypes)
    (initialState : certified.moduleStructure.State)
    (inputs : List ports.inputs.Values) :
    ∃ outputs finalState,
      certified.moduleStructure.Executes initialState inputs outputs finalState ∧
        certified.contract.Accepts inputs outputs := by
  rcases certified.execution_exists initialState inputs with
    ⟨outputs, finalState, execution⟩
  exact ⟨outputs, finalState, execution, certified.accepts_execution execution⟩

end FifoCertified

end Silean.Contracts.Fifo
