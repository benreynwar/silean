import Silean.Contracts.Fifo.FifoContract
import Silean.Interfaces.FifoPorts

namespace Silean.Contracts.Fifo

open Silean

/-- The latency-independent FIFO contract shared by all implementations using
the standard FIFO ports. -/
def standardContract (element : SignalType) (capacity : Nat) :
    FifoContract (Interfaces.Fifo.ports element) (Interfaces.Fifo.payloadTypes element) where
  sink := Interfaces.Fifo.sink element
  source := Interfaces.Fifo.source element
  reset := .reset
  resetType := rfl
  capacity := capacity

@[simp] theorem standardContract_resetAsserted (element : SignalType)
    (capacity : Nat) (inputs : (Interfaces.Fifo.ports element).inputs.Values) :
    (standardContract element capacity).resetAsserted inputs = inputs .reset := rfl

@[simp] theorem standardContract_inputTransfer (element : SignalType)
    (capacity : Nat) (inputs : (Interfaces.Fifo.ports element).inputs.Values)
    (outputs : (Interfaces.Fifo.ports element).outputs.Values) :
    (standardContract element capacity).inputTransfer inputs outputs =
      bif inputs .inputValid && outputs .inputReady
        then [(inputs .inputData, ())] else [] := by
  cases inputValid : inputs .inputValid <;>
    cases inputReady : outputs .inputReady <;>
    simp [FifoContract.inputTransfer, standardContract, Interfaces.Fifo.sink,
      Interfaces.ValidReadySink.sample, Interfaces.ValidReadySample.transferredPayload?,
      Interfaces.ValidReadySample.transfers, inputValid, inputReady,
      Interfaces.Fifo.inputMap, Interfaces.Fifo.outputMap, SignalType.Denote,
      SignalSelection.project, SignalMap.select] <;> rfl

@[simp] theorem standardContract_outputTransfer (element : SignalType)
    (capacity : Nat) (inputs : (Interfaces.Fifo.ports element).inputs.Values)
    (outputs : (Interfaces.Fifo.ports element).outputs.Values) :
    (standardContract element capacity).outputTransfer inputs outputs =
      bif outputs .outputValid && inputs .outputReady
        then [(outputs .outputData, ())] else [] := by
  cases outputValid : outputs .outputValid <;>
    cases outputReady : inputs .outputReady <;>
    simp [FifoContract.outputTransfer, standardContract, Interfaces.Fifo.source,
      Interfaces.ValidReadySource.sample, Interfaces.ValidReadySample.transferredPayload?,
      Interfaces.ValidReadySample.transfers, outputValid, outputReady,
      Interfaces.Fifo.inputMap, Interfaces.Fifo.outputMap, SignalType.Denote,
      SignalSelection.project, SignalMap.select] <;> rfl

end Silean.Contracts.Fifo
