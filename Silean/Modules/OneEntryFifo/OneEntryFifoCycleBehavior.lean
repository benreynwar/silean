import Silean.Contracts.Fifo.FifoCycleBehavior
import Silean.Modules.OneEntryFifo.OneEntryFifo

namespace Silean.Modules.OneEntryFifo

open Silean
open Contracts.Fifo.Cycle

/-! Packages the one-entry FIFO's cycle behavior in the generic form used by
serial FIFO composition. -/

def oneEntryCycleBehavior (signalType : SignalType) : CycleBehavior signalType where
  state := OneEntryFifo.stateMap signalType
  forward := fun inputValid inputData state =>
    (state .storedValid || inputValid,
      bif state .storedValid then state .storedData else inputData)
  ready := fun outputReady state => outputReady || !state .storedValid
  nextState := (OneEntryFifo.stateRule signalType).apply

theorem oneEntryCycleBehavior_cycleContract (signalType : SignalType) :
    (oneEntryCycleBehavior signalType).cycleContract =
      OneEntryFifo.cycleContract signalType := rfl

noncomputable def oneEntryCertified (signalType : SignalType) :
    CertifiedCycleBehavior signalType where
  cycleBehavior := oneEntryCycleBehavior signalType
  moduleStructure := OneEntryFifo.moduleStructure signalType
  certification := (OneEntryFifo.certification signalType).transportContract
    (oneEntryCycleBehavior_cycleContract signalType).symm

end Silean.Modules.OneEntryFifo
