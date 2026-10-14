import Silean.Interfaces.FifoPorts
import Silean.Naming.ModuleNaming

namespace Silean.Naming.FifoPorts

open Silean

/-- Names the canonical FIFO valid/ready boundary and its payload shape. -/
def portsWithNaming (element : SignalType)
    (elementNaming : SignalTypeNaming element) :
    ModulePortsNaming (Silean.Interfaces.Fifo.ports element) where
  inputs := ⟨fun
    | .inputValid => "input_valid"
    | .inputData => "input_data"
    | .outputReady => "output_ready"
    | .reset => "reset"⟩
  outputs := ⟨fun
    | .outputValid => "output_valid"
    | .outputData => "output_data"
    | .inputReady => "input_ready"⟩
  inputTypes := fun
    | .inputValid | .outputReady | .reset => .bit
    | .inputData => elementNaming
  outputTypes := fun
    | .outputValid | .inputReady => .bit
    | .outputData => elementNaming

def ports (element : SignalType) :
    ModulePortsNaming (Silean.Interfaces.Fifo.ports element) :=
  portsWithNaming element (.positional element)

end Silean.Naming.FifoPorts
