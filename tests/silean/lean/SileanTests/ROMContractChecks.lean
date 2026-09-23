import Silean.Modules.ROM.ROM

assert_not_imported Silean.Modules.ROM.Internal.ROMStructure
assert_not_imported Silean.Modules.ROM.Internal.ROMVerification

namespace SileanTests.ROMContract

open Silean
open Silean.Modules

def contents : Fin (ROM.entryCount 2) → Bool
  | 0 => false
  | 1 => true
  | 2 => true
  | 3 => false

def inputs : (ROM.ports .bit 2).inputs.Values
  | .address => fun | 0 => false | 1 => true

def result := ((ROM.cycleContract .bit 2 contents).evaluate
  inputs SignalMap.emptyValues).1 .data

-- Address bits `10` select entry two.
#guard result

example {element : SignalType} {addressWidth : Nat}
    {table : Fin (ROM.entryCount addressWidth) → element.Denote}
    {step : (ROM.cycleContract element addressWidth table).Step}
    (allowed :
      (ROM.cycleContract element addressWidth table).Allows step) :
    step.outputs .data =
      ROM.lookup addressWidth table (step.inputs .address) :=
  ROM.cycleContract.data element addressWidth table allowed

end SileanTests.ROMContract
