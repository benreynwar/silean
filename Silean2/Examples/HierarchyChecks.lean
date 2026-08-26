import Silean2.Examples.Not
import Silean2.Examples.DoubleNot
import Silean2.Modules.BitMux
import Silean2.Examples.RepeatedDualNot

namespace Silean2.Examples.HierarchyChecks

open Silean2

example : Primitives.not.localState = emptySignalMap := rfl

example : Examples.HierarchicalDualNot.moduleStructure.structuralState =
    .children Examples.HierarchicalDualNot.Instance Examples.HierarchicalDualNot.instances.names
      (fun | .forwardNot | .backwardNot => .local emptySignalMap) := by
  simp [Examples.HierarchicalDualNot.moduleStructure, ModuleStructure.structuralState,
    Examples.HierarchicalDualNot.body, Examples.HierarchicalDualNot.context,
      Examples.HierarchicalDualNot.instances]
  funext name
  cases name <;> rfl

example : Examples.RepeatedDualNot.moduleStructure.structuralState =
    .children Examples.RepeatedDualNot.Instance Examples.RepeatedDualNot.instances.names
      (fun | .first | .second => Examples.HierarchicalDualNot.moduleStructure.structuralState) := by
  simp [Examples.RepeatedDualNot.moduleStructure, ModuleStructure.structuralState,
    Examples.RepeatedDualNot.body, Examples.RepeatedDualNot.context, Examples.RepeatedDualNot.instances,
    Examples.RepeatedDualNot.childStructure]
  funext name
  cases name <;> rfl

example : (Examples.RepeatedDualNot.instances.names.ordinal .first).val = 0 := rfl
example : (Examples.RepeatedDualNot.instances.names.ordinal .second).val = 1 := rfl

example : (Examples.RepeatedDualNot.childStructure .first).structuralState =
    Examples.HierarchicalDualNot.moduleStructure.structuralState := rfl

example : Examples.RepeatedDualNot.childStructure .first =
    Examples.HierarchicalDualNot.moduleStructure := rfl

example : Examples.RepeatedDualNot.childStructure .second =
    Examples.HierarchicalDualNot.moduleStructure := rfl

def firstForwardNot : ModulePath Examples.RepeatedDualNot.moduleStructure Primitives.not.ports :=
  .child .first (.child .forwardNot .here)

def secondForwardNot : ModulePath Examples.RepeatedDualNot.moduleStructure Primitives.not.ports :=
  .child .second (.child .forwardNot .here)

example : firstForwardNot.depth = 2 := rfl
example : secondForwardNot.depth = 2 := rfl

example : firstForwardNot ≠ secondForwardNot := by
  intro equal
  cases equal

def firstForwardOutput : PrimitiveOutputOccurrence Examples.RepeatedDualNot.moduleStructure :=
  ⟨Primitives.not, firstForwardNot, .output⟩

def secondForwardOutput : PrimitiveOutputOccurrence Examples.RepeatedDualNot.moduleStructure :=
  ⟨Primitives.not, secondForwardNot, .output⟩

example : firstForwardOutput.path.depth = 2 := rfl
example : secondForwardOutput.path.depth = 2 := rfl

end Silean2.Examples.HierarchyChecks
