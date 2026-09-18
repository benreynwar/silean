import Silean.Modules.SerialDepthFifo.Internal.SerialDepthFifoVerification

/-! # Serial-depth FIFO cycle theorems

These results expose the exact boundary behavior of the recursively assembled
FIFO without exposing the recursive certification objects used to build the
proof.
-/

namespace Silean.Modules.SerialDepthFifo

open Silean
open Contracts.Fifo.Cycle

section AllowedStep

variable {signalType : SignalType} {depth : Nat} {positive : 0 < depth}
  {step : (cycleContract signalType depth positive).Step}
  (allowed : (cycleContract signalType depth positive).Allows step)

include allowed

/-- The forward outputs are exactly those computed by the recursively composed
cycle behavior. -/
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

/-- Input readiness is exactly that computed by the recursive cycle behavior. -/
theorem inputReady_of_allowed :
    step.outputs .inputReady =
      (cycleBehavior signalType depth positive).ready
        (step.inputs .outputReady) step.currentState :=
  ((cycleBehavior signalType depth positive).readyRule_holds_iff
    step.inputs step.currentState step.outputs).mp (allowed.1 .ready)

/-- The next state is the state transition of the recursive cycle behavior. -/
theorem nextState_of_allowed :
    step.nextState =
      (cycleBehavior signalType depth positive).nextState
        step.inputs step.currentState := by
  simpa [cycleContract] using allowed.2

end AllowedStep

/-- The recursively assembled positive-depth FIFO implements its exact cycle
contract at the shared boundary-step interface. -/
theorem implements_contract (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    Contracts.Cycle.Implements
      (moduleStructure signalType depth positive)
      (cycleContract signalType depth positive)
      (certification signalType depth positive).stateCorresponds :=

    (certification signalType depth positive).implements

@[simp] theorem certified_moduleStructure (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certified signalType depth positive).moduleStructure =
      moduleStructure signalType depth positive := rfl

@[simp] theorem certified_cycleContract (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certified signalType depth positive).cycleContract =
      cycleContract signalType depth positive := rfl

end Silean.Modules.SerialDepthFifo
