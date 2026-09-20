import Silean.Modules.BitMux.BitMuxDerived
import SileanTests.Fixtures.DualNot
import SileanTests.Fixtures.RepeatedDualNot

namespace SileanTests.ModuleCycleContract

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

def dualInputs : SileanTests.Fixtures.DualNot.ports.inputs.Values
  | .forward => true
  | .backward => false

example : SileanTests.Fixtures.DualNot.forwardRule.readsInputs.labels =
    [SileanTests.Fixtures.DualNot.Input.forward] := rfl

example : SileanTests.Fixtures.DualNot.backwardRule.readsInputs.labels =
    [SileanTests.Fixtures.DualNot.Input.backward] := rfl

example : SileanTests.Fixtures.DualNot.cycleContract.writtenOutputs =
    [SileanTests.Fixtures.DualNot.Output.forward, SileanTests.Fixtures.DualNot.Output.backward] := rfl

example : (SileanTests.Fixtures.DualNot.forwardRule.target
    (SileanTests.Fixtures.DualNot.forwardRule.readsInputs.project dualInputs)
    SignalMap.emptyValues) .value = false := rfl

example : (SileanTests.Fixtures.DualNot.backwardRule.target
    (SileanTests.Fixtures.DualNot.backwardRule.readsInputs.project dualInputs)
    SignalMap.emptyValues) .value = true := rfl

example : SileanTests.Fixtures.RepeatedDualNot.cycleContract.state.labels.values = [] := rfl

end SileanTests.ModuleCycleContract
