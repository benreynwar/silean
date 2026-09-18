import Silean.Modules.Fifo.Internal.FifoCycleVerification

/-! # Pointer FIFO cycle theorems

This file is the supported structural proof interface for the pointer and
register-bank FIFO. Its exact boundary behavior remains distinct from the
latency-independent FIFO refinement.
-/

namespace Silean.Modules.Fifo

open Silean

/-- The pointer/register-bank hierarchy implements its exact cycle contract. -/
theorem implements_cycle_contract (element : SignalType)
    (addressWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure element addressWidth)
      (cycleContract element addressWidth)
      (certification element addressWidth).stateCorresponds :=
  (certification element addressWidth).implements

end Silean.Modules.Fifo
