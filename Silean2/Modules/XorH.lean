import Silean2.FoundationsH

namespace Silean2.Modules.Xor

open Silean2.Foundations

abbrev xorPorts : ModulePorts := {
  nInputs := 2
  nOutputs := 1
  inputTypes := fun _ => .bit
  outputTypes := fun _ => .bit
}

abbrev left : xorPorts.InputKey := 0
abbrev right : xorPorts.InputKey := 0
abbrev result : xorPorts.OutputKey := 0

def xorFunction (inputs : xorPorts.InputValues) : xorPorts.OutputValues :=
  fun _ => (inputs left) ^^ (inputs right)

def xorSpec := Spec.ofFunction xorFunction

end Silean2.Modules.Xor
