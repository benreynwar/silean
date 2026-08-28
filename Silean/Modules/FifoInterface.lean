import Silean.DeriveEnumeration
import Silean.Foundation.ModulePorts

namespace Silean.Modules.Fifo

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

end Silean.Modules.Fifo
