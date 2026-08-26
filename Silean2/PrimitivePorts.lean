import Silean2.Primitive

namespace Silean2.Primitives

open Silean2

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

def unaryInputMap : SignalMap :=
  EnumeratedMap.of UnaryInput fun | .input => .bit

def binaryInputMap : SignalMap :=
  EnumeratedMap.of BinaryInput fun | .left | .right => .bit

def singleOutputMap : SignalMap :=
  EnumeratedMap.of SingleOutput fun | .output => .bit

def registerStateMap : SignalMap :=
  EnumeratedMap.of RegisterState fun | .stored => .bit

def unaryPorts : ModulePorts := ⟨unaryInputMap, singleOutputMap⟩

def binaryPorts : ModulePorts := ⟨binaryInputMap, singleOutputMap⟩

end Silean2.Primitives
