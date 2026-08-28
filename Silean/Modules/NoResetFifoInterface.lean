import Silean.ModuleCycleContract

namespace Silean.Modules.NoResetFifo

open Silean

inductive Input
  | inputValid
  | inputData
  | outputReady
deriving Enumeration

inductive Output
  | outputValid
  | outputData
  | inputReady
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun
    | .inputValid | .outputReady => .bit
    | .inputData => signalType

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun
    | .outputValid | .inputReady => .bit
    | .outputData => signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap signalType⟩

inductive Rule
  | forward
  | ready
deriving Enumeration

end Silean.Modules.NoResetFifo
