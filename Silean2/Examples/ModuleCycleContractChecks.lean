import Silean2.Modules.BitMux
import Silean2.Examples.DualNot
import Silean2.Examples.RepeatedDualNot

namespace Silean2.Examples.ModuleCycleContractChecks

open Silean2

def muxInputs : Modules.BitMux.ports.inputs.Values
  | .select => true
  | .whenFalse => false
  | .whenTrue => true

example : Modules.BitMux.cycleContract.state.labels.values = [] := rfl

example : Modules.BitMux.selectRule.readsInputs.labels =
    [Modules.BitMux.Input.select, Modules.BitMux.Input.whenFalse, Modules.BitMux.Input.whenTrue] := rfl

example : Modules.BitMux.selectRule.writesOutputs.labels =
    [Modules.BitMux.Output.result] := rfl

example : Modules.BitMux.selectRule.target
    (Modules.BitMux.selectRule.readsInputs.project muxInputs)
    SignalMap.emptyValues = (true, ()) := rfl

example : Modules.BitMux.cycleContract.writtenOutputs = [Modules.BitMux.Output.result] := rfl

def dualInputs : Examples.DualNot.ports.inputs.Values
  | .forward => true
  | .backward => false

example : Examples.DualNot.forwardRule.readsInputs.labels =
    [Examples.DualNot.Input.forward] := rfl

example : Examples.DualNot.backwardRule.readsInputs.labels =
    [Examples.DualNot.Input.backward] := rfl

example : Examples.DualNot.cycleContract.writtenOutputs =
    [Examples.DualNot.Output.forward, Examples.DualNot.Output.backward] := rfl

example : Examples.DualNot.forwardRule.target
    (Examples.DualNot.forwardRule.readsInputs.project dualInputs)
    SignalMap.emptyValues = (false, ()) := rfl

example : Examples.DualNot.backwardRule.target
    (Examples.DualNot.backwardRule.readsInputs.project dualInputs)
    SignalMap.emptyValues = (true, ()) := rfl

example : Examples.RepeatedDualNot.cycleContract.state.labels.values = [] := rfl

end Silean2.Examples.ModuleCycleContractChecks
