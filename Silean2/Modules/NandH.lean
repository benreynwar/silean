import Silean2.FoundationsH

namespace Silean2.Modules.Nand

open Silean2.Foundations

abbrev nandPorts : ModulePorts := {
  nInputs := 2
  nOutputs := 1
  inputTypes := fun _ => .bit
  outputTypes := fun _ => .bit
}

abbrev left : nandPorts.InputKey := 0
abbrev right : nandPorts.InputKey := 0
abbrev result : nandPorts.OutputKey := 1

def nandFunction (inputs : nandPorts.InputValues) : nandPorts.OutputValues :=
  fun _ => !((inputs left) && (inputs right))

def nandSpec := Spec.ofFunction nandFunction

end Silean2.Modules.Nand
