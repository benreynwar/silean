import Silean.Modules.BitMux.BitMux
import Silean.Examples.Fixtures.DualNot
import Silean.Examples.Fixtures.RepeatedDualNot

namespace Silean.Examples.Checks.ModuleCycleContract

open Silean

def muxInputs : Modules.BitMux.ports.inputs.Values
  | .select => true
  | .whenFalse => false
  | .whenTrue => true

example : Modules.BitMux.cycleContract.state.labels.values = [] := rfl

example : Modules.BitMux.selectRule.readsInputs.labels =
    [Modules.BitMux.Input.select, Modules.BitMux.Input.whenFalse, Modules.BitMux.Input.whenTrue] := rfl

example : Modules.BitMux.selectRule.writesOutputs.labels =
    [Modules.BitMux.Output.result] := rfl

def muxOutputs : Modules.BitMux.ports.outputs.Values
  | .result => true

example : Modules.BitMux.selectRule.Holds muxInputs SignalMap.emptyValues muxOutputs :=
  (Modules.BitMux.selectRule_holds_iff _ _ _).2 rfl

example : Modules.BitMux.cycleContract.writtenOutputs = [Modules.BitMux.Output.result] := rfl

def dualInputs : Examples.Fixtures.DualNot.ports.inputs.Values
  | .forward => true
  | .backward => false

example : Examples.Fixtures.DualNot.forwardRule.readsInputs.labels =
    [Examples.Fixtures.DualNot.Input.forward] := rfl

example : Examples.Fixtures.DualNot.backwardRule.readsInputs.labels =
    [Examples.Fixtures.DualNot.Input.backward] := rfl

example : Examples.Fixtures.DualNot.cycleContract.writtenOutputs =
    [Examples.Fixtures.DualNot.Output.forward, Examples.Fixtures.DualNot.Output.backward] := rfl

example : (Examples.Fixtures.DualNot.forwardRule.target
    (Examples.Fixtures.DualNot.forwardRule.readsInputs.project dualInputs)
    SignalMap.emptyValues) .value = false := rfl

example : (Examples.Fixtures.DualNot.backwardRule.target
    (Examples.Fixtures.DualNot.backwardRule.readsInputs.project dualInputs)
    SignalMap.emptyValues) .value = true := rfl

example : Examples.Fixtures.RepeatedDualNot.cycleContract.state.labels.values = [] := rfl

end Silean.Examples.Checks.ModuleCycleContract
