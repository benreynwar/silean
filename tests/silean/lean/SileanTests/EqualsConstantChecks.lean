import Silean.FIRRTL
import Silean.Modules.EqualsConstant.EqualsConstantDerived

namespace SileanTests.EqualsConstant

open Silean Silean.FIRRTL

def threeBits : SignalType := .vector 3 .bit
def five : threeBits.Denote := fun | 0 => true | 1 => false | 2 => true

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.EqualsConstant.ports threeBits) :=
  Modules.EqualsConstant.certified threeBits five

def matchingInputs : (Modules.EqualsConstant.ports threeBits).inputs.Values
  | .value => five

def differentInputs : (Modules.EqualsConstant.ports threeBits).inputs.Values
  | .value => fun | 0 => true | 1 => true | 2 => true

#guard ((Modules.EqualsConstant.cycleContract threeBits five).evaluate
  matchingInputs SignalMap.emptyValues).1 .result

#guard !((Modules.EqualsConstant.cycleContract threeBits five).evaluate
  differentInputs SignalMap.emptyValues).1 .result

example {step : (Modules.EqualsConstant.cycleContract signalType constant).Step}
    (allowed : (Modules.EqualsConstant.cycleContract signalType constant).Allows step) :
    step.outputs .result = true ↔ step.inputs .value = constant :=
  Modules.EqualsConstant.result_eq_true_iff_of_allowed
    signalType constant allowed

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderCircuit (Modules.EqualsConstant.naming threeBits five) with
  | .error _ => false
  | .ok text => ["public module EqualsConstant",
      "input value : UInt<1>[3]", "output result : UInt<1>",
      "inst constant_0", "inst equality_0",
      "connect equality_0.right, constant_0.value"].all (contains text)

end SileanTests.EqualsConstant
