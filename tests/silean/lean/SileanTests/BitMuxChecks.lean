import Silean.Modules.BitMux.BitMuxDerived

namespace SileanTests.BitMux

open Silean

def inputs (select whenFalse whenTrue : Bool) : Modules.BitMux.ports.inputs.Values
  | .select => select
  | .whenFalse => whenFalse
  | .whenTrue => whenTrue

def result (select whenFalse whenTrue : Bool) : Bool :=
  ((Modules.BitMux.cycleContract.evaluate
    (inputs select whenFalse whenTrue) SignalMap.emptyValues).1 .result)

#guard !result false false true
#guard result false true false
#guard !result true true false
#guard result true false true

example : Modules.BitMux.description.ImplementsCycleContract
    Modules.BitMux.cycleContract Modules.BitMux.Naming.ports :=
  Modules.BitMux.construction_correct

example {step : Modules.BitMux.moduleStructure.Step}
    (realizes : Modules.BitMux.moduleStructure.Realizes step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse :=
  Modules.BitMux.result_of_realization realizes

end SileanTests.BitMux
