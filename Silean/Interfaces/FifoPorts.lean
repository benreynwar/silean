import Silean.Foundation.DeriveEnumeration
import Silean.Foundation.ModulePorts
import Silean.Interfaces.ValidReady

namespace Silean.Interfaces.Fifo

open Silean

inductive Input
  | inputValid
  | inputData
  | outputReady
  | reset
deriving Enumeration

inductive Output
  | outputValid
  | outputData
  | inputReady
deriving Enumeration

@[reducible] def inputMap (element : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun
    | .inputValid | .outputReady | .reset => .bit
    | .inputData => element

@[reducible] def outputMap (element : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun
    | .outputValid | .inputReady => .bit
    | .outputData => element

@[reducible] def ports (element : SignalType) : ModulePorts :=
  ⟨inputMap element, outputMap element⟩

abbrev payloadTypes (element : SignalType) : SignalTypes :=
  .cons element .nil

/-- The input valid/ready channel at a FIFO boundary. -/
def sink (element : SignalType) :
    Interfaces.ValidReadySink (ports element) (payloadTypes element) where
  valid := .inputValid
  validType := rfl
  ready := .inputReady
  readyType := rfl
  payload := (inputMap element).select .inputData

/-- The output valid/ready channel at a FIFO boundary. -/
def source (element : SignalType) :
    Interfaces.ValidReadySource (ports element) (payloadTypes element) where
  valid := .outputValid
  validType := rfl
  ready := .outputReady
  readyType := rfl
  payload := (outputMap element).select .outputData

end Silean.Interfaces.Fifo
