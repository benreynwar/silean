import Silean.Contracts.Fifo.FifoContract
import Silean.Contracts.Cycle.CycleImplementation

namespace Silean.Contracts.Fifo

/-! A private-proof adapter from exact cycle certification to the public,
latency-independent FIFO contract. -/

structure FifoCycleRefinement
    (cycleCertified : Contracts.Cycle.ModuleCycleCertified ports)
    (fifoContract : FifoContract ports payloadTypes) where
  /-- States reachable after synchronization that obey the representation invariant. -/
  Invariant : cycleCertified.cycleContract.state.Values → Prop
  /-- Abstract queue represented by an exact cycle state. -/
  queue : cycleCertified.cycleContract.state.Values → fifoContract.Queue
  /-- Valid represented queues fit within the declared capacity. -/
  bounded : ∀ state, Invariant state → (queue state).length ≤ fifoContract.capacity
  /-- Reset establishes the invariant and an empty queue. -/
  reset : ∀ inputs state,
    fifoContract.resetAsserted inputs = true →
      let next := cycleCertified.cycleContract.stateRule.apply inputs state
      Invariant next ∧ queue next = []
  /-- Every ordinary cycle preserves the invariant and FIFO transfer equation. -/
  ordinary : ∀ inputs state,
    Invariant state → fifoContract.resetAsserted inputs = false →
      let evaluated := cycleCertified.cycleContract.evaluate inputs state
      Invariant evaluated.2 ∧
        queue state ++ fifoContract.inputTransfer inputs evaluated.1 =
          fifoContract.outputTransfer inputs evaluated.1 ++ queue evaluated.2

namespace FifoCycleRefinement

variable {ports : ModulePorts} {payloadTypes : SignalTypes}
variable {cycleCertified : Contracts.Cycle.ModuleCycleCertified ports}
variable {fifoContract : FifoContract ports payloadTypes}

private def synchronizedQueue
    (refinement : FifoCycleRefinement cycleCertified fifoContract)
    (state : cycleCertified.cycleContract.state.Values)
    (valid : refinement.Invariant state) : fifoContract.BoundedQueue :=
  ⟨refinement.queue state, refinement.bounded state valid⟩

private def Aligned
    (refinement : FifoCycleRefinement cycleCertified fifoContract)
    (state : cycleCertified.cycleContract.state.Values) :
    fifoContract.Synchronization → Prop
  | none => True
  | some queue =>
      ∃ valid : refinement.Invariant state,
        queue = refinement.synchronizedQueue state valid

private theorem refineExecution
    (refinement : FifoCycleRefinement cycleCertified fifoContract) :
    ∀ {initialState finalState : cycleCertified.moduleStructure.State}
      {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
      {cycleState : cycleCertified.cycleContract.state.Values}
      {synchronization : fifoContract.Synchronization},
      cycleCertified.stateCorresponds cycleState initialState →
      refinement.Aligned cycleState synchronization →
      cycleCertified.moduleStructure.Executes initialState inputs outputs finalState →
      ∃ finalCycleState finalSynchronization,
        cycleCertified.stateCorresponds finalCycleState finalState ∧
        refinement.Aligned finalCycleState finalSynchronization ∧
        fifoContract.TraceMatches synchronization inputs outputs finalSynchronization := by
  intro initialState finalState inputs outputs cycleState synchronization
    corresponds aligned execution
  induction execution generalizing cycleState synchronization with
  | nil =>
      exact ⟨cycleState, synchronization, corresponds, aligned, .nil synchronization⟩
  | cons input output transition rest induction =>
      rcases cycleCertified.realization_matches_evaluate cycleState
          corresponds transition with
        ⟨evaluatedOutputEq, nextCorresponds⟩
      have actualOutputEq : output =
          (cycleCertified.cycleContract.evaluate input cycleState).1 :=
        evaluatedOutputEq
      cases resetEq : fifoContract.resetAsserted input
      · cases synchronization with
        | none =>
            rcases induction (synchronization := none) nextCorresponds trivial with
              ⟨finalCycleState, finalSynchronization, finalCorresponds,
                finalAligned, finalTrace⟩
            exact ⟨finalCycleState, finalSynchronization, finalCorresponds,
              finalAligned, .cons input output (.beforeReset resetEq) finalTrace⟩
        | some queue =>
            rcases aligned with ⟨valid, queueEq⟩
            rcases refinement.ordinary input cycleState valid resetEq with
              ⟨nextValid, preserves⟩
            let nextQueue := refinement.synchronizedQueue
              (cycleCertified := cycleCertified) _ nextValid
            have preservesActual : queue.1 ++ fifoContract.inputTransfer input output =
                fifoContract.outputTransfer input output ++ nextQueue.1 := by
              subst queue
              rw [actualOutputEq]
              exact preserves
            rcases induction (synchronization := some nextQueue) nextCorresponds
                ⟨nextValid, rfl⟩ with
              ⟨finalCycleState, finalSynchronization, finalCorresponds,
                finalAligned, finalTrace⟩
            exact ⟨finalCycleState, finalSynchronization, finalCorresponds,
              finalAligned, .cons input output
                (.ordinary resetEq preservesActual) finalTrace⟩
      · rcases refinement.reset input cycleState resetEq with
          ⟨nextValid, nextEmpty⟩
        let nextQueue := refinement.synchronizedQueue
          (cycleCertified := cycleCertified) _ nextValid
        have queueEq : nextQueue = fifoContract.emptyQueue := by
          apply Subtype.ext
          exact nextEmpty
        rcases induction (synchronization := fifoContract.resetSynchronization)
            nextCorresponds ⟨nextValid, queueEq.symm⟩ with
          ⟨finalCycleState, finalSynchronization, finalCorresponds,
            finalAligned, finalTrace⟩
        exact ⟨finalCycleState, finalSynchronization, finalCorresponds,
          finalAligned, .cons input output (.reset resetEq) finalTrace⟩

noncomputable def certify
    (refinement : FifoCycleRefinement cycleCertified fifoContract) :
    FifoCertified ports payloadTypes where
  moduleStructure := cycleCertified.moduleStructure
  contract := fifoContract
  hasSolution := cycleCertified.structuralCertification.hasSolution
  implements := by
    intro initialState inputs outputs finalState execution
    rcases cycleCertified.hasCorrespondingState initialState with
      ⟨cycleState, corresponds⟩
    rcases refinement.refineExecution (synchronization := none)
        corresponds trivial execution with
      ⟨_, finalSynchronization, _, _, trace⟩
    exact ⟨finalSynchronization, trace⟩

end FifoCycleRefinement

end Silean.Contracts.Fifo
