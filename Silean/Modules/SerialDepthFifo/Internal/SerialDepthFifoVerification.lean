import Silean.Composition.FifoSerialCertification
import Silean.Modules.OneEntryFifo.OneEntryFifoCycleBehavior
import Silean.Modules.SerialDepthFifo.SerialDepthFifo

namespace Silean.Modules.SerialDepthFifo

open Silean
open Contracts.Fifo.Cycle
open OneEntryFifo

/-! Structural cycle certification for every positive serial FIFO depth.
The recursive proof combines already-certified one-entry FIFOs through the
generic serial layer and never inspects either child's implementation. -/

namespace Internal

noncomputable def certifiedCycleBehaviorFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → CertifiedCycleBehavior signalType
  | 0 => oneEntryCertified signalType
  | additionalDepth + 1 =>
      Composition.FifoSerial.certifiedCycleBehavior (oneEntryCertified signalType)
        (certifiedCycleBehaviorFromAdditional signalType additionalDepth)

@[simp] theorem certifiedCycleBehaviorFromAdditional_behavior
    (signalType : SignalType) (additionalDepth : Nat) :
    (certifiedCycleBehaviorFromAdditional signalType additionalDepth).cycleBehavior =
      cycleBehaviorFromAdditional signalType additionalDepth := by
  induction additionalDepth with
  | zero => rfl
  | succ additionalDepth induction =>
      simp only [certifiedCycleBehaviorFromAdditional, cycleBehaviorFromAdditional,
        Composition.FifoSerial.certifiedCycleBehavior, oneEntryCertified]
      rw [induction]

@[simp] theorem certifiedCycleBehaviorFromAdditional_moduleStructure
    (signalType : SignalType) (additionalDepth : Nat) :
    (certifiedCycleBehaviorFromAdditional signalType additionalDepth).moduleStructure =
      moduleStructureFromAdditional signalType additionalDepth := by
  induction additionalDepth with
  | zero => rfl
  | succ additionalDepth induction =>
      simp only [certifiedCycleBehaviorFromAdditional, moduleStructureFromAdditional,
        Composition.FifoSerial.certifiedCycleBehavior, oneEntryCertified]
      rw [induction]

private noncomputable def certifiedCycleBehavior (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) : CertifiedCycleBehavior signalType :=
  let assembled := certifiedCycleBehaviorFromAdditional signalType (additionalDepth depth)
  { cycleBehavior := cycleBehaviorFromAdditional signalType (additionalDepth depth)
    moduleStructure := moduleStructure signalType depth positive
    certification := (assembled.certification.transportStructure
      (by
        simp only [moduleStructure]
        exact certifiedCycleBehaviorFromAdditional_moduleStructure signalType
          (additionalDepth depth))).transportContract
      (congrArg CycleBehavior.cycleContract
        (certifiedCycleBehaviorFromAdditional_behavior signalType (additionalDepth depth))) }

end Internal

noncomputable def certification (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType depth positive)
      (cycleContract signalType depth positive) :=
  (Internal.certifiedCycleBehavior signalType depth positive).certification

noncomputable def certified (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    Contracts.Cycle.ModuleCycleCertified (Silean.Interfaces.Fifo.ports signalType) :=
  (certification signalType depth positive).bundle

end Silean.Modules.SerialDepthFifo
