import Silean.FIRRTL
import Silean.Modules.CarrySaveTree.CarrySaveTreeDerived

namespace SileanTests.CarrySaveTree

open Silean Silean.FIRRTL
open Silean.Modules.CarrySaveTree

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

private def closedCircuitHasAdderCount (operandCount expected : Nat) : Bool :=
  match renderCircuit (naming 4 operandCount) with
  | .error _ => false
  | .ok text => contains text "public module carry_save_tree" &&
      occurrences text "inst carry_save_adder_" == expected

#guard closedCircuitHasAdderCount 0 0
#guard closedCircuitHasAdderCount 1 0
#guard closedCircuitHasAdderCount 2 0
#guard closedCircuitHasAdderCount 3 1
#guard closedCircuitHasAdderCount 4 2
#guard closedCircuitHasAdderCount 5 3
#guard closedCircuitHasAdderCount 6 4
#guard closedCircuitHasAdderCount 8 6

end SileanTests.CarrySaveTree
