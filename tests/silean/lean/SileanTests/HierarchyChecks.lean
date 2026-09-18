import SileanTests.Fixtures.Not
import SileanTests.Fixtures.DoubleNot
import Silean.Modules.BitMux.BitMux
import SileanTests.Fixtures.RepeatedDualNot

namespace SileanTests.Hierarchy

open Silean

example : Primitives.not.localState = emptySignalMap := rfl

example : SileanTests.Fixtures.HierarchicalDualNot.moduleStructure.structuralState =
    .children
      { Key := SileanTests.Fixtures.HierarchicalDualNot.Instance
        keys := SileanTests.Fixtures.HierarchicalDualNot.instancePorts.names
        value := fun _ => .leaf emptySignalMap } := by
  simp [SileanTests.Fixtures.HierarchicalDualNot.moduleStructure, ModuleStructure.structuralState,
    SileanTests.Fixtures.HierarchicalDualNot.body, SileanTests.Fixtures.HierarchicalDualNot.context,
      SileanTests.Fixtures.HierarchicalDualNot.instancePorts]
  funext name
  cases name <;> rfl

example : SileanTests.Fixtures.RepeatedDualNot.moduleStructure.structuralState =
    .children
      { Key := SileanTests.Fixtures.RepeatedDualNot.Instance
        keys := SileanTests.Fixtures.RepeatedDualNot.instancePorts.names
        value := fun _ =>
          SileanTests.Fixtures.HierarchicalDualNot.moduleStructure.structuralState } := by
  simp [SileanTests.Fixtures.RepeatedDualNot.moduleStructure, ModuleStructure.structuralState,
    SileanTests.Fixtures.RepeatedDualNot.body, SileanTests.Fixtures.RepeatedDualNot.context, SileanTests.Fixtures.RepeatedDualNot.instancePorts,
    SileanTests.Fixtures.RepeatedDualNot.childStructure]
  funext name
  cases name <;> rfl

example : (SileanTests.Fixtures.RepeatedDualNot.instancePorts.names.ordinal .first).val = 0 := rfl
example : (SileanTests.Fixtures.RepeatedDualNot.instancePorts.names.ordinal .second).val = 1 := rfl

example : (SileanTests.Fixtures.RepeatedDualNot.childStructure .first).structuralState =
    SileanTests.Fixtures.HierarchicalDualNot.moduleStructure.structuralState := rfl

example : SileanTests.Fixtures.RepeatedDualNot.childStructure .first =
    SileanTests.Fixtures.HierarchicalDualNot.moduleStructure := rfl

example : SileanTests.Fixtures.RepeatedDualNot.childStructure .second =
    SileanTests.Fixtures.HierarchicalDualNot.moduleStructure := rfl

end SileanTests.Hierarchy
