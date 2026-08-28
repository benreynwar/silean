import Silean.Examples.Fixtures.Not
import Silean.Examples.Fixtures.DoubleNot
import Silean.Modules.BitMux
import Silean.Examples.Fixtures.RepeatedDualNot

namespace Silean.Examples.Checks.Hierarchy

open Silean

example : Primitives.not.localState = emptySignalMap := rfl

example : Examples.Fixtures.HierarchicalDualNot.moduleStructure.structuralState =
    .children Examples.Fixtures.HierarchicalDualNot.Instance Examples.Fixtures.HierarchicalDualNot.instances.names
      (fun | .forwardNot | .backwardNot => .local emptySignalMap) := by
  simp [Examples.Fixtures.HierarchicalDualNot.moduleStructure, ModuleStructure.structuralState,
    Examples.Fixtures.HierarchicalDualNot.body, Examples.Fixtures.HierarchicalDualNot.context,
      Examples.Fixtures.HierarchicalDualNot.instances]
  funext name
  cases name <;> rfl

example : Examples.Fixtures.RepeatedDualNot.moduleStructure.structuralState =
    .children Examples.Fixtures.RepeatedDualNot.Instance Examples.Fixtures.RepeatedDualNot.instances.names
      (fun | .first | .second => Examples.Fixtures.HierarchicalDualNot.moduleStructure.structuralState) := by
  simp [Examples.Fixtures.RepeatedDualNot.moduleStructure, ModuleStructure.structuralState,
    Examples.Fixtures.RepeatedDualNot.body, Examples.Fixtures.RepeatedDualNot.context, Examples.Fixtures.RepeatedDualNot.instances,
    Examples.Fixtures.RepeatedDualNot.childStructure]
  funext name
  cases name <;> rfl

example : (Examples.Fixtures.RepeatedDualNot.instances.names.ordinal .first).val = 0 := rfl
example : (Examples.Fixtures.RepeatedDualNot.instances.names.ordinal .second).val = 1 := rfl

example : (Examples.Fixtures.RepeatedDualNot.childStructure .first).structuralState =
    Examples.Fixtures.HierarchicalDualNot.moduleStructure.structuralState := rfl

example : Examples.Fixtures.RepeatedDualNot.childStructure .first =
    Examples.Fixtures.HierarchicalDualNot.moduleStructure := rfl

example : Examples.Fixtures.RepeatedDualNot.childStructure .second =
    Examples.Fixtures.HierarchicalDualNot.moduleStructure := rfl

end Silean.Examples.Checks.Hierarchy
