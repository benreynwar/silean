import Silean.Modules.RegisterBank.Internal.RegisterBankVerification

/-! # Register-bank theorems

The public interface describes complete boundary steps. The one-hot decoder,
per-entry gates and registers, read muxes, schedules, and hierarchy state
correspondence remain verification details under `Internal/`.
-/

namespace Silean.Modules.RegisterBank

open Silean

/-- The concrete register-bank hierarchy implements its exact cycle contract
at the shared boundary-step interface. -/
theorem implements_contract (element : SignalType)
    (addressWidth readCount : Nat) :
    Contracts.Cycle.Implements
      (moduleStructure element addressWidth readCount)
      (cycleContract element addressWidth readCount)
      (certification element addressWidth readCount).stateCorresponds :=
  (certification element addressWidth readCount).implements

end Silean.Modules.RegisterBank
