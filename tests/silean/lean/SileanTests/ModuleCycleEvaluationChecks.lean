import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Modules.BitMux.BitMuxDerived
import SileanTests.Fixtures.DualNot
import Silean.Modules.EnabledRegister.EnabledRegister

namespace SileanTests.ModuleCycleEvaluation

open Silean

def muxInputs : Modules.BitMux.ports.inputs.Values
  | .select => true
  | .whenFalse => false
  | .whenTrue => true

example : Modules.BitMux.cycleContract.applyOutputRules muxInputs SignalMap.emptyValues
    .result = true := rfl

example : Modules.BitMux.cycleContract.Allows
    (Modules.BitMux.cycleContract.evaluateStep muxInputs SignalMap.emptyValues) :=
  Modules.BitMux.cycleContract.evaluateStep_allowed _ _

def dualInputs : SileanTests.Fixtures.DualNot.ports.inputs.Values
  | .forward => true
  | .backward => false

example : SileanTests.Fixtures.DualNot.cycleContract.applyOutputRules dualInputs
    SignalMap.emptyValues .forward = false := rfl

example : SileanTests.Fixtures.DualNot.cycleContract.applyOutputRules dualInputs
    SignalMap.emptyValues .backward = true := rfl

def falseState : Primitives.registerStateMap.Values
  | .stored => false

def holdInputs : (Modules.EnabledRegister.ports .bit).inputs.Values
  | .data => true
  | .enable => false

def updateInputs : (Modules.EnabledRegister.ports .bit).inputs.Values
  | .data | .enable => true

example : (Modules.EnabledRegister.cycleContract .bit).applyOutputRules holdInputs falseState
    .q = false := rfl

example : ((Modules.EnabledRegister.cycleContract .bit).evaluate holdInputs falseState).2
    .stored = false := rfl

example : ((Modules.EnabledRegister.cycleContract .bit).evaluate updateInputs falseState).2
    .stored = true := rfl

end SileanTests.ModuleCycleEvaluation
