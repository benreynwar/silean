import Silean.FIRRTL
import Silean.Modules.CarrySaveLayer.CarrySaveLayerDerived

namespace SileanTests.CarrySaveLayer

open Silean Silean.FIRRTL
open Silean.Modules.CarrySaveLayer

example (width operandCount : Nat)
    {step : (moduleStructure width operandCount).Step}
    (realizes : (moduleStructure width operandCount).Realizes step) :
    contract width operandCount step.inputs step.outputs :=
  contract_of_realization width operandCount realizes

example (width operandCount : Nat) :
    ModuleStructuralCertification (moduleStructure width operandCount) :=
  structuralCertification width operandCount

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def rendersWithAdderCount (operandCount expected : Nat) : Bool :=
  match renderRootModule (naming 4 operandCount) with
  | .error _ => false
  | .ok text => contains text "public module CarrySaveLayer_4" &&
      occurrences text "inst carry_save_adder_" == expected

#guard rendersWithAdderCount 0 0
#guard rendersWithAdderCount 1 0
#guard rendersWithAdderCount 2 0
#guard rendersWithAdderCount 3 1
#guard rendersWithAdderCount 8 2

end SileanTests.CarrySaveLayer
