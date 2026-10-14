import Silean.Composition.FifoSerialRefinement
import Silean.Modules.OneEntryFifo.OneEntryFifoDerived
import Silean.Modules.SerialDepthFifo.Internal.SerialDepthFifoVerification

/-! # Serial-depth FIFO refinement verification

This internal proof recursively lifts the one-entry FIFO refinement through
generic serial composition. The public derived facade exports only the
resulting certified FIFO and its stable identities.
-/

namespace Silean.Modules.SerialDepthFifo.Internal

open Silean
open Contracts.Fifo.Cycle
open OneEntryFifo

private noncomputable def refinementFromAdditional (element : SignalType) :
    (additionalDepth : Nat) →
      Contracts.Fifo.FifoCycleRefinement
        (certifiedCycleBehaviorFromAdditional element additionalDepth).certified
        (Silean.Contracts.Fifo.standardContract element (additionalDepth + 1))
  | 0 => OneEntryFifo.fifoRefinement element
  | additionalDepth + 1 => by
      change Contracts.Fifo.FifoCycleRefinement
        (Composition.FifoSerial.certifiedCycleBehavior
          (oneEntryCertified element)
          (certifiedCycleBehaviorFromAdditional element additionalDepth)).certified
        (Silean.Contracts.Fifo.standardContract element (additionalDepth + 2))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Composition.FifoSerial.serialRefinement
          (oneEntryCertified element)
          (certifiedCycleBehaviorFromAdditional element additionalDepth)
          1 (additionalDepth + 1)
          (OneEntryFifo.fifoRefinement element)
          (refinementFromAdditional element additionalDepth)

private noncomputable def fifoCertifiedFromAdditional (element : SignalType)
    (additionalDepth : Nat) :
    Contracts.Fifo.FifoCertified (Silean.Interfaces.Fifo.ports element)
      (Silean.Interfaces.Fifo.payloadTypes element) :=
  (refinementFromAdditional element additionalDepth).certify

noncomputable def fifoCertified (element : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    Contracts.Fifo.FifoCertified (Silean.Interfaces.Fifo.ports element)
      (Silean.Interfaces.Fifo.payloadTypes element) := by
  have capacityEq : additionalDepth depth + 1 = depth := additionalDepth_eq positive
  simpa [fifoCertifiedFromAdditional, Contracts.Fifo.FifoCycleRefinement.certify,
    moduleStructure, capacityEq] using
    fifoCertifiedFromAdditional element (additionalDepth depth)

@[simp] theorem fifoCertified_moduleStructure (element : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (fifoCertified element depth positive).moduleStructure =
      moduleStructure element depth positive := by
  simp [fifoCertified, fifoCertifiedFromAdditional,
    Contracts.Fifo.FifoCycleRefinement.certify, moduleStructure,
    additionalDepth_eq positive]
  exact certifiedCycleBehaviorFromAdditional_moduleStructure element
    (additionalDepth depth)

@[simp] theorem fifoCertified_contract (element : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (fifoCertified element depth positive).contract =
      Silean.Contracts.Fifo.standardContract element depth := by
  simp [fifoCertified, fifoCertifiedFromAdditional,
    Contracts.Fifo.FifoCycleRefinement.certify, additionalDepth_eq positive]

end Silean.Modules.SerialDepthFifo.Internal
