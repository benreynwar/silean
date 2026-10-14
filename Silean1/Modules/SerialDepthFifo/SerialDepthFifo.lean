import Silean.Contracts.Fifo.FifoCycleBehavior
import Silean.Modules.OneEntryFifo.OneEntryFifo

/-! # Serial-depth FIFO

A positive-depth FIFO formed by serially composing fall-through one-entry
FIFO behaviors. This file is the human-facing semantic interface: it states
the recursive exact-cycle behavior, its contract, and the laws needed to use
that contract.

The recursive hardware hierarchy is deliberately not duplicated as a
handwritten builder program. It lives under `Internal`; placement and
certification are exposed by `SerialDepthFifoDerived.lean`.
-/

namespace Silean.Modules.SerialDepthFifo

open Silean
open Contracts.Fifo.Cycle

/-- Number of entries after the required first entry. -/
def additionalDepth (depth : Nat) : Nat := depth - 1

theorem additionalDepth_eq {depth : Nat} (positive : 0 < depth) :
    additionalDepth depth + 1 = depth := by
  unfold additionalDepth
  omega

def cycleBehaviorFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → CycleBehavior signalType
  | 0 => OneEntryFifo.cycleBehavior signalType
  | additionalDepth + 1 =>
      (OneEntryFifo.cycleBehavior signalType).serial
        (cycleBehaviorFromAdditional signalType additionalDepth)

def cycleBehavior (signalType : SignalType) (depth : Nat) (_positive : 0 < depth) :
    CycleBehavior signalType :=
  cycleBehaviorFromAdditional signalType (additionalDepth depth)

@[simp] theorem cycleBehavior_one (signalType : SignalType)
    (positive : 0 < 1) :
    cycleBehavior signalType 1 positive = OneEntryFifo.cycleBehavior signalType := rfl

@[simp] theorem cycleBehavior_step (signalType : SignalType)
    (additionalDepth : Nat) (positive : 0 < additionalDepth + 2) :
    cycleBehavior signalType (additionalDepth + 2) positive =
      (OneEntryFifo.cycleBehavior signalType).serial
        (cycleBehavior signalType (additionalDepth + 1) (by omega)) := by
  simp only [cycleBehavior, SerialDepthFifo.additionalDepth, Nat.add_sub_cancel]
  rfl

def cycleContract (signalType : SignalType) (depth : Nat) (positive : 0 < depth) :
    Contracts.Cycle.ModuleCycleContract (Silean.Interfaces.Fifo.ports signalType) :=
  (cycleBehavior signalType depth positive).cycleContract

section AllowedStep

variable {signalType : SignalType} {depth : Nat} {positive : 0 < depth}
  {step : (cycleContract signalType depth positive).Step}
  (allowed : (cycleContract signalType depth positive).Allows step)

include allowed

/-- The forward outputs are those computed by the composed behavior. -/
theorem forward_of_allowed :
    step.outputs .outputValid =
        ((cycleBehavior signalType depth positive).forward
          (step.inputs .inputValid) (step.inputs .inputData)
          step.currentState).1 ∧
      step.outputs .outputData =
        ((cycleBehavior signalType depth positive).forward
          (step.inputs .inputValid) (step.inputs .inputData)
          step.currentState).2 :=
  ((cycleBehavior signalType depth positive).forwardRule_holds_iff
    step.inputs step.currentState step.outputs).mp (allowed.1 .forward)

/-- Input readiness is that computed by the composed behavior. -/
theorem inputReady_of_allowed :
    step.outputs .inputReady =
      (cycleBehavior signalType depth positive).ready
        (step.inputs .outputReady) step.currentState :=
  ((cycleBehavior signalType depth positive).readyRule_holds_iff
    step.inputs step.currentState step.outputs).mp (allowed.1 .ready)

/-- The next state is the composed behavior's state transition. -/
theorem nextState_of_allowed :
    step.nextState =
      (cycleBehavior signalType depth positive).nextState
        step.inputs step.currentState := by
  simpa [cycleContract] using allowed.2

end AllowedStep

end Silean.Modules.SerialDepthFifo
