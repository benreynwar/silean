import Silean2.FoundationsH
import Silean2.Modules.NandH

namespace Silean2.Modules.Not

open Silean2.Foundations

-- Specification of a NOT gate

abbrev notPorts : ModulePorts := {
  nInputs := 1
  nOutputs := 1
  inputTypes := fun _ => .bit
  outputTypes := fun _ => .bit
}

abbrev x : notPorts.InputKey := 0
abbrev result : notPorts.OutputKey := 0

def notFunction (inputs : notPorts.InputValues) : notPorts.OutputValues :=
  fun _ => !(inputs x)

def notSpec := Spec.ofFunction notFunction


-- Implementation of a NOT gate with a NAND gate

open Silean2.Modules

def notFromNand : ModuleBody := {
  ports := notPorts
  nChildren := 1
  childPorts := fun _ => Nand.nandPorts
  childInputDrivers := fun _ _ => Source.input x
  outputDrivers := fun _ => Source.childOutput 0 Nand.result
}

namespace NotFromNand

  abbrev childSpecs : ChildSpecs notFromNand := fun _ => Nand.nandSpec

end NotFromNand

end Silean2.Modules.Not
