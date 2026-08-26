import Silean2.ModuleCycleEvaluation
import Silean2.Modules.BitMux
import Silean2.Examples.DualNot
import Silean2.Modules.EnabledRegister

namespace Silean2.Examples.ModuleCycleEvaluationChecks

open Silean2

def muxInputs : Modules.BitMux.ports.inputs.Values
  | .select => true
  | .whenFalse => false
  | .whenTrue => true

example : Modules.BitMux.cycleContract.applyOutputRules muxInputs SignalMap.emptyValues
    .result = true := rfl

example : Modules.BitMux.cycleContract.EvaluatesTo muxInputs SignalMap.emptyValues
    (Modules.BitMux.cycleContract.applyOutputRules muxInputs SignalMap.emptyValues)
    SignalMap.emptyValues :=
  Modules.BitMux.cycleContract.evaluate_evaluatesTo _ _

def dualInputs : Examples.DualNot.ports.inputs.Values
  | .forward => true
  | .backward => false

example : Examples.DualNot.cycleContract.applyOutputRules dualInputs
    SignalMap.emptyValues .forward = false := rfl

example : Examples.DualNot.cycleContract.applyOutputRules dualInputs
    SignalMap.emptyValues .backward = true := rfl

def falseState : Primitives.registerStateMap.Values
  | .stored => false

def holdInputs : (Modules.EnabledRegister.ports .bit).inputs.Values
  | .value => true
  | .enable => false

def updateInputs : (Modules.EnabledRegister.ports .bit).inputs.Values
  | .value | .enable => true

example : (Modules.EnabledRegister.cycleContract .bit).applyOutputRules holdInputs falseState
    .value = false := rfl

example : ((Modules.EnabledRegister.cycleContract .bit).evaluate holdInputs falseState).2
    .stored = false := rfl

example : ((Modules.EnabledRegister.cycleContract .bit).evaluate updateInputs falseState).2
    .stored = true := rfl

end Silean2.Examples.ModuleCycleEvaluationChecks
