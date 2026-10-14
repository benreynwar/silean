import Silean.Contracts.Fifo.FifoCycleRefinement
import Silean.Contracts.Fifo.FifoPortContract
import Silean.Composition.FifoSerialCertification

namespace Silean.Composition.FifoSerial

open Silean
open Contracts.Fifo.Cycle

/-! Proves that serial composition preserves abstract FIFO behavior. The
logical queue is the downstream queue followed by the upstream queue; this
file defines no additional hardware. -/

/-- Serial composition preserves FIFO behavior. The proof uses only each
child's cycle behavior and FIFO refinement; it does not inspect either child
structure or its structural proof. -/
def serialRefinement
    (upstream downstream : CertifiedCycleBehavior element)
    (upstreamCapacity downstreamCapacity : Nat)
    (upstreamRefinement : Contracts.Fifo.FifoCycleRefinement upstream.certified
      (Silean.Contracts.Fifo.standardContract element upstreamCapacity))
    (downstreamRefinement : Contracts.Fifo.FifoCycleRefinement downstream.certified
      (Silean.Contracts.Fifo.standardContract element downstreamCapacity)) :
    Contracts.Fifo.FifoCycleRefinement (certifiedCycleBehavior upstream downstream).certified
      (Silean.Contracts.Fifo.standardContract element (upstreamCapacity + downstreamCapacity)) where
  Invariant := fun state =>
    upstreamRefinement.Invariant (leftState state) ∧
      downstreamRefinement.Invariant (rightState state)
  queue := fun state =>
    downstreamRefinement.queue (rightState state) ++
      upstreamRefinement.queue (leftState state)
  bounded := by
    intro state valid
    change (upstream.cycleBehavior.serial downstream.cycleBehavior).state.Values at state
    simp only [List.length_append]
    have upstreamBound := upstreamRefinement.bounded _ valid.1
    have downstreamBound := downstreamRefinement.bounded _ valid.2
    change (upstreamRefinement.queue (leftState state)).length ≤ upstreamCapacity at upstreamBound
    change (downstreamRefinement.queue (rightState state)).length ≤ downstreamCapacity at downstreamBound
    change _ ≤ upstreamCapacity + downstreamCapacity
    omega
  reset := by
    intro inputs state reset
    change (upstream.cycleBehavior.serial downstream.cycleBehavior).state.Values at state
    let upstreamInput := CycleBehavior.serialUpstreamInputs upstream.cycleBehavior
      downstream.cycleBehavior inputs (leftState state) (rightState state)
    let downstreamInput := CycleBehavior.serialDownstreamInputs upstream.cycleBehavior
      downstream.cycleBehavior inputs (leftState state) (rightState state)
    have upstreamReset :
        (Silean.Contracts.Fifo.standardContract element upstreamCapacity).resetAsserted upstreamInput = true := by
      exact reset
    have downstreamReset :
        (Silean.Contracts.Fifo.standardContract element downstreamCapacity).resetAsserted downstreamInput = true := by
      exact reset
    rcases upstreamRefinement.reset upstreamInput (leftState state) upstreamReset with
      ⟨upstreamValid, upstreamEmpty⟩
    rcases downstreamRefinement.reset downstreamInput (rightState state) downstreamReset with
      ⟨downstreamValid, downstreamEmpty⟩
    change
      (upstreamRefinement.Invariant
          (upstream.cycleBehavior.nextState upstreamInput (leftState state)) ∧
        downstreamRefinement.Invariant
          (downstream.cycleBehavior.nextState downstreamInput (rightState state))) ∧
      downstreamRefinement.queue
          (downstream.cycleBehavior.nextState downstreamInput (rightState state)) ++
        upstreamRefinement.queue
          (upstream.cycleBehavior.nextState upstreamInput (leftState state)) = []
    simp only [CertifiedCycleBehavior.certified_stateRule_apply] at upstreamValid upstreamEmpty downstreamValid downstreamEmpty
    constructor
    · exact ⟨upstreamValid, downstreamValid⟩
    · calc
        _ = [] ++ upstreamRefinement.queue
            (upstream.cycleBehavior.nextState upstreamInput (leftState state)) :=
          congrArg (fun head => head ++ _) downstreamEmpty
        _ = [] ++ [] := congrArg (fun tail => [] ++ tail) upstreamEmpty
        _ = [] := rfl
  ordinary := by
    intro inputs state valid notReset
    change (upstream.cycleBehavior.serial downstream.cycleBehavior).state.Values at state
    let upstreamInput := CycleBehavior.serialUpstreamInputs upstream.cycleBehavior
      downstream.cycleBehavior inputs (leftState state) (rightState state)
    let downstreamInput := CycleBehavior.serialDownstreamInputs upstream.cycleBehavior
      downstream.cycleBehavior inputs (leftState state) (rightState state)
    have upstreamNotReset :
        (Silean.Contracts.Fifo.standardContract element upstreamCapacity).resetAsserted upstreamInput = false := by
      exact notReset
    have downstreamNotReset :
        (Silean.Contracts.Fifo.standardContract element downstreamCapacity).resetAsserted downstreamInput = false := by
      exact notReset
    rcases upstreamRefinement.ordinary upstreamInput (leftState state) valid.1
        upstreamNotReset with ⟨upstreamValid, upstreamEquation⟩
    rcases downstreamRefinement.ordinary downstreamInput (rightState state) valid.2
        downstreamNotReset with ⟨downstreamValid, downstreamEquation⟩
    simp only [CertifiedCycleBehavior.certified_cycleContract] at upstreamValid upstreamEquation downstreamValid downstreamEquation
    constructor
    · exact ⟨upstreamValid, downstreamValid⟩
    ·
      simp only [CertifiedCycleBehavior.certified_cycleContract]
      have inputTransferEq :
          (Silean.Contracts.Fifo.standardContract element upstreamCapacity).inputTransfer upstreamInput
              (upstream.cycleBehavior.cycleContract.evaluate upstreamInput
                (leftState state)).1 =
            (Silean.Contracts.Fifo.standardContract element (upstreamCapacity + downstreamCapacity)).inputTransfer
              inputs (((upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract.evaluate
                inputs state).1) := by
        simp [Contracts.Fifo.standardContract_inputTransfer, upstreamInput,
          CycleBehavior.serialUpstreamInputs,
          CycleBehavior.serial] <;> rfl
      have middleTransferEq :
          (Silean.Contracts.Fifo.standardContract element upstreamCapacity).outputTransfer upstreamInput
              (upstream.cycleBehavior.cycleContract.evaluate upstreamInput
                (leftState state)).1 =
            (Silean.Contracts.Fifo.standardContract element downstreamCapacity).inputTransfer downstreamInput
              (downstream.cycleBehavior.cycleContract.evaluate downstreamInput
                (rightState state)).1 := by
        simp [Contracts.Fifo.standardContract_outputTransfer, Contracts.Fifo.standardContract_inputTransfer,
          upstreamInput, downstreamInput, CycleBehavior.serialUpstreamInputs,
          CycleBehavior.serialDownstreamInputs] <;> rfl
      have outputTransferEq :
          (Silean.Contracts.Fifo.standardContract element downstreamCapacity).outputTransfer downstreamInput
              (downstream.cycleBehavior.cycleContract.evaluate downstreamInput
                (rightState state)).1 =
            (Silean.Contracts.Fifo.standardContract element (upstreamCapacity + downstreamCapacity)).outputTransfer
              inputs (((upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract.evaluate
                inputs state).1) := by
        simp [Contracts.Fifo.standardContract_outputTransfer, downstreamInput,
          CycleBehavior.serialDownstreamInputs, CycleBehavior.serial] <;> rfl
      rw [inputTransferEq] at upstreamEquation
      rw [middleTransferEq] at upstreamEquation
      rw [outputTransferEq] at downstreamEquation
      simp only [certifiedCycleBehavior, CycleBehavior.evaluate_nextState]
      change
        (downstreamRefinement.queue (rightState state) ++
            upstreamRefinement.queue (leftState state)) ++
            (Silean.Contracts.Fifo.standardContract element (upstreamCapacity + downstreamCapacity)).inputTransfer
              inputs ((upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract.evaluate
                inputs state).1 =
          (Silean.Contracts.Fifo.standardContract element (upstreamCapacity + downstreamCapacity)).outputTransfer
              inputs ((upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract.evaluate
                inputs state).1 ++
            (downstreamRefinement.queue
                (downstream.cycleBehavior.cycleContract.evaluate downstreamInput
                  (rightState state)).2 ++
              upstreamRefinement.queue
                (upstream.cycleBehavior.cycleContract.evaluate upstreamInput
                  (leftState state)).2)
      calc
        _ = downstreamRefinement.queue (rightState state) ++
            (upstreamRefinement.queue (leftState state) ++
              (Silean.Contracts.Fifo.standardContract element
                (upstreamCapacity + downstreamCapacity)).inputTransfer inputs
                  ((upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract.evaluate
                    inputs state).1) := List.append_assoc ..
        _ = downstreamRefinement.queue (rightState state) ++
            ((Silean.Contracts.Fifo.standardContract element downstreamCapacity).inputTransfer downstreamInput
                (downstream.cycleBehavior.cycleContract.evaluate downstreamInput
                  (rightState state)).1 ++
              upstreamRefinement.queue
                (upstream.cycleBehavior.cycleContract.evaluate upstreamInput
                  (leftState state)).2) := congrArg (fun tail =>
                    downstreamRefinement.queue (rightState state) ++ tail)
                  upstreamEquation
        _ = (downstreamRefinement.queue (rightState state) ++
              (Silean.Contracts.Fifo.standardContract element downstreamCapacity).inputTransfer downstreamInput
                (downstream.cycleBehavior.cycleContract.evaluate downstreamInput
                  (rightState state)).1) ++
            upstreamRefinement.queue
              (upstream.cycleBehavior.cycleContract.evaluate upstreamInput
                (leftState state)).2 := (List.append_assoc ..).symm
        _ = ((Silean.Contracts.Fifo.standardContract element
                (upstreamCapacity + downstreamCapacity)).outputTransfer inputs
                  ((upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract.evaluate
                    inputs state).1 ++
              downstreamRefinement.queue
                (downstream.cycleBehavior.cycleContract.evaluate downstreamInput
                  (rightState state)).2) ++
            upstreamRefinement.queue
              (upstream.cycleBehavior.cycleContract.evaluate upstreamInput
                (leftState state)).2 := congrArg (fun head => head ++
                  upstreamRefinement.queue
                    (upstream.cycleBehavior.cycleContract.evaluate upstreamInput
                      (leftState state)).2) downstreamEquation
        _ = _ := List.append_assoc ..

end Silean.Composition.FifoSerial
