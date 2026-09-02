import Silean.FIRRTL
import Silean.Modules.EqualsConstant

namespace Silean.Examples.Checks.EqualsConstant

open Silean Silean.FIRRTL

def threeBits : SignalType := .vector 3 .bit
def five : threeBits.Denote := fun | 0 => true | 1 => false | 2 => true

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.EqualsConstant.ports threeBits) :=
  Modules.EqualsConstant.certified threeBits five

example : (Modules.EqualsConstant.moduleStructure threeBits five).HasNoBlackboxes := by
  native_decide

def matchingInputs : (Modules.EqualsConstant.ports threeBits).inputs.Values
  | .value => five

def differentInputs : (Modules.EqualsConstant.ports threeBits).inputs.Values
  | .value => fun | 0 => true | 1 => true | 2 => true

#guard ((Modules.EqualsConstant.cycleContract threeBits five).evaluate
  matchingInputs SignalMap.emptyValues).1 .result

#guard !((Modules.EqualsConstant.cycleContract threeBits five).evaluate
  differentInputs SignalMap.emptyValues).1 .result

example (inputs : (Modules.EqualsConstant.ports signalType).inputs.Values)
    (outputs : (Modules.EqualsConstant.ports signalType).outputs.Values)
    (holds : (Modules.EqualsConstant.outputRule signalType constant).Holds
      inputs SignalMap.emptyValues outputs) :
    outputs .result = true ↔ inputs .value = constant :=
  Modules.EqualsConstant.output_eq_true_iff_of_holds signalType constant inputs
    SignalMap.emptyValues outputs holds

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderCircuit (Modules.EqualsConstant.Naming.naming threeBits five) with
  | .error _ => false
  | .ok text => ["public module equals_constant_structural",
      "input value : UInt<1>[3]", "output result : UInt<1>",
      "inst constant", "inst equality",
      "connect equality.right, constant.value"].all (contains text)

end Silean.Examples.Checks.EqualsConstant
