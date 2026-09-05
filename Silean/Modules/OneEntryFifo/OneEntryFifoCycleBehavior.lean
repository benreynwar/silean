import Silean.Contracts.Fifo.FifoCycleBehavior
import Silean.Modules.OneEntryFifo.OneEntryFifoCycleCertified

namespace Silean.Modules.OneEntryFifo

open Silean
open Contracts.Fifo.Cycle

/-! Packages the one-entry FIFO's cycle behavior in the generic form used by
serial FIFO composition. -/

noncomputable def oneEntryCertified (signalType : SignalType) :
    CertifiedCycleBehavior signalType where
  cycleBehavior := OneEntryFifo.cycleBehavior signalType
  moduleStructure := OneEntryFifo.moduleStructure signalType
  certification := OneEntryFifo.certification signalType

end Silean.Modules.OneEntryFifo
