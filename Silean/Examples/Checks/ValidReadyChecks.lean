import Silean.Interfaces.ValidReady
import Silean.Interfaces.FifoPorts

namespace Silean.Examples.Checks.ValidReady

open Silean

abbrev PayloadTypes (element : SignalType) : SignalTypes :=
  .cons element .nil

def fifoSink (element : SignalType) :
    Interfaces.ValidReadySink (Silean.Interfaces.Fifo.ports element) (PayloadTypes element) where
  valid := .inputValid
  validType := rfl
  ready := .inputReady
  readyType := rfl
  payload := (Silean.Interfaces.Fifo.inputMap element).select .inputData

def fifoSource (element : SignalType) :
    Interfaces.ValidReadySource (Silean.Interfaces.Fifo.ports element) (PayloadTypes element) where
  valid := .outputValid
  validType := rfl
  ready := .outputReady
  readyType := rfl
  payload := (Silean.Interfaces.Fifo.outputMap element).select .outputData

def bitInputs (inputValid inputData outputReady reset : Bool) :
    (Silean.Interfaces.Fifo.ports .bit).inputs.Values
  | .inputValid => inputValid
  | .inputData => inputData
  | .outputReady => outputReady
  | .reset => reset

def bitOutputs (outputValid outputData inputReady : Bool) :
    (Silean.Interfaces.Fifo.ports .bit).outputs.Values
  | .outputValid => outputValid
  | .outputData => outputData
  | .inputReady => inputReady

example : (fifoSink .bit).sample
    (bitInputs true true false false) (bitOutputs false false true) =
      ⟨true, true, (true, ())⟩ := rfl

example : (fifoSource .bit).sample
    (bitInputs false false true false) (bitOutputs true true false) =
      ⟨true, true, (true, ())⟩ := rfl

def sinkCycles : List
    ((Silean.Interfaces.Fifo.ports .bit).inputs.Values ×
      (Silean.Interfaces.Fifo.ports .bit).outputs.Values) :=
  [ (bitInputs true false false false, bitOutputs false false false)
  , (bitInputs true true false false, bitOutputs false false true)
  , (bitInputs false false false false, bitOutputs false false true) ]

example : (fifoSink .bit).transferredPayloads sinkCycles = [(true, ())] := rfl

def sourceCycles : List
    ((Silean.Interfaces.Fifo.ports .bit).inputs.Values ×
      (Silean.Interfaces.Fifo.ports .bit).outputs.Values) :=
  [ (bitInputs false false false false, bitOutputs true false false)
  , (bitInputs false false true false, bitOutputs true true false)
  , (bitInputs false false true false, bitOutputs false false false) ]

example : (fifoSource .bit).transferredPayloads sourceCycles = [(true, ())] := rfl

example (left right : List
    ((Silean.Interfaces.Fifo.ports .bit).inputs.Values ×
      (Silean.Interfaces.Fifo.ports .bit).outputs.Values)) :
    (fifoSink .bit).transferredPayloads (left ++ right) =
      (fifoSink .bit).transferredPayloads left ++
        (fifoSink .bit).transferredPayloads right := by
  exact Interfaces.ValidReadySink.transferredPayloads_append (fifoSink .bit) left right

end Silean.Examples.Checks.ValidReady
