import Silean.Structure.Primitive

namespace Silean.Primitives

open Silean

inductive UnaryInput
  | input
deriving Enumeration

inductive BinaryInput
  | left
  | right
deriving Enumeration

inductive SingleOutput
  | output
deriving Enumeration

inductive RegisterState
  | stored
deriving Enumeration

@[reducible] def unaryInputMap : SignalMap :=
  EnumeratedMap.of UnaryInput fun | .input => .bit

@[reducible] def binaryInputMap : SignalMap :=
  EnumeratedMap.of BinaryInput fun | .left | .right => .bit

@[reducible] def singleOutputMap : SignalMap :=
  EnumeratedMap.of SingleOutput fun | .output => .bit

@[reducible] def registerStateMap : SignalMap :=
  EnumeratedMap.of RegisterState fun | .stored => .bit

@[reducible] def unaryPorts : ModulePorts := ⟨unaryInputMap, singleOutputMap⟩

@[reducible] def binaryPorts : ModulePorts := ⟨binaryInputMap, singleOutputMap⟩

@[reducible] def constantPorts : ModulePorts := ⟨emptySignalMap, singleOutputMap⟩

end Silean.Primitives
