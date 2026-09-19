import Silean.Modules.OneEntryFifo.Internal.OneEntryFifoFifoVerification

/-! # One-entry FIFO refinement theorems -/

namespace Silean.Modules.OneEntryFifo

open Silean

/-! The internal refinement interprets the stored-valid bit and payload as a
logical queue of length zero or one. Its refinement witness is public because
larger FIFO constructions compose it directly; users needing only the final
latency-independent result can use `fifoCertified`. -/

/-- The exact cycle-certified implementation refines the standard
capacity-one FIFO contract. This is the compositional interface used by
larger FIFO constructions. -/
def fifoRefinement (element : SignalType) :
    Contracts.Fifo.FifoCycleRefinement (certified element)
      (Silean.Contracts.Fifo.standardContract element 1) :=
  Internal.cycleRefinement element

/-- The one-entry implementation satisfies the standard capacity-one FIFO
contract. -/
noncomputable def fifoCertified (element : SignalType) :
    Contracts.Fifo.FifoCertified (Silean.Interfaces.Fifo.ports element)
      (Silean.Interfaces.Fifo.payloadTypes element) :=
  (fifoRefinement element).certify

@[simp] theorem fifoCertified_moduleStructure (element : SignalType) :
    (fifoCertified element).moduleStructure = moduleStructure element := rfl

@[simp] theorem fifoCertified_contract (element : SignalType) :
    (fifoCertified element).contract =
      Silean.Contracts.Fifo.standardContract element 1 := rfl

end Silean.Modules.OneEntryFifo
