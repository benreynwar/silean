import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Modules.BitMux
import Silean.Examples.Fixtures.DualNot
import Silean.Modules.EnabledRegister

namespace Silean.Examples.Checks.ModuleCycleEvaluation

open Silean

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

def dualInputs : Examples.Fixtures.DualNot.ports.inputs.Values
  | .forward => true
  | .backward => false

example : Examples.Fixtures.DualNot.cycleContract.applyOutputRules dualInputs
    SignalMap.emptyValues .forward = false := rfl

example : Examples.Fixtures.DualNot.cycleContract.applyOutputRules dualInputs
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

end Silean.Examples.Checks.ModuleCycleEvaluation
