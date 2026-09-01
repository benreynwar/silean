import Silean.Primitives

namespace Silean.Examples.Checks.Foundation

open Silean

def binaryInputs : Primitives.binaryInputMap.Values
  | .left => false
  | .right => true

example : binaryInputs .left = false := rfl
example : binaryInputs .right = true := rfl

example : Primitives.binaryInputMap.labels.values =
    [Primitives.BinaryInput.left, Primitives.BinaryInput.right] := rfl

example : (Primitives.binaryInputMap.labels.ordinal .left).val = 0 := rfl
example : (Primitives.binaryInputMap.labels.ordinal .right).val = 1 := rfl
example : (Primitives.singleOutputMap.labels.ordinal .output).val = 0 := rfl

def byte : SignalType := .vector 8 .bit

inductive PacketField
  | valid
  | payload
deriving Enumeration

def packetFields : SignalMap :=
  EnumeratedMap.of PacketField fun
    | .valid => .bit
    | .payload => byte

def packetType : SignalType := packetFields.tupleType

def emptyByte : byte.Denote := fun _ => false

def packetFieldValues : packetFields.Values
  | .valid => true
  | .payload => emptyByte

example : packetFieldValues .valid = true := rfl
example : packetFieldValues .payload 0 = false := rfl

def packetValue : packetType.Denote := (true, (emptyByte, ()))

example : packetFields.types = [.bit, byte] := rfl
example : packetValue.1 = true := rfl
example : packetValue.2.1 0 = false := rfl

inductive RenamedPacketField
  | enabled
  | data
deriving Enumeration

def renamedPacketFields : SignalMap :=
  EnumeratedMap.of RenamedPacketField fun
    | .enabled => .bit
    | .data => byte

example : renamedPacketFields.tupleType = packetType := rfl

inductive ThreeLabel
  | first
  | second
  | third
deriving Enumeration

example : (inferInstance : Enumeration ThreeLabel).values =
    [.first, .second, .third] := rfl

example : ((inferInstance : Enumeration ThreeLabel).ordinal .third).val = 2 :=
  rfl

#eval Primitives.binaryInputMap.labels.ordinal Primitives.BinaryInput.right
end Silean.Examples.Checks.Foundation
