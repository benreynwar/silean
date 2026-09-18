import Silean.Modules.Fifo.Internal.FifoFifoVerification

/-! # Pointer FIFO refinement theorems

The exact cycle contract is exposed by `FifoCycleTheorems.lean`. This file
states the separate result that those cycles implement the latency-independent
FIFO contract, while the queue invariant proof remains under `Internal/`.
-/

namespace Silean.Modules.Fifo

open Silean Silean.Interfaces.Fifo

/-- The pointer/register-bank implementation satisfies the standard bounded
FIFO contract with capacity `2 ^ addressWidth`. -/
noncomputable def fifoCertified (element : SignalType)
    (addressWidth : Nat) :
    Contracts.Fifo.FifoCertified (ports element) (payloadTypes element) :=
  (Internal.fifoRefinement element addressWidth).certify

@[simp] theorem fifoCertified_moduleStructure (element : SignalType)
    (addressWidth : Nat) :
    (fifoCertified element addressWidth).moduleStructure =
      moduleStructure element addressWidth := rfl

@[simp] theorem fifoCertified_contract (element : SignalType)
    (addressWidth : Nat) :
    (fifoCertified element addressWidth).contract =
      Contracts.Fifo.standardContract element
        (Properties.capacity addressWidth) := rfl

end Silean.Modules.Fifo
