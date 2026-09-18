import SileanTests.Fixtures.RepeatedDualNot
import Silean.FIRRTL
import Silean.Naming.ModuleNaming
import Silean.Naming.PrimitiveNaming

namespace SileanTests.ModuleClosure

open Silean Silean.FIRRTL

example : (ModuleStructure.primitive Primitives.not).HasNoBlackboxes := by
  decide

example : SileanTests.Fixtures.RepeatedDualNot.moduleStructure.HasNoBlackboxes := by
  decide

#guard SileanTests.Fixtures.RepeatedDualNot.moduleStructure.hasNoBlackboxes

example : ¬(ModuleStructure.blackbox Primitives.not).HasNoBlackboxes := by
  decide

#guard !(ModuleStructure.blackbox Primitives.not).hasNoBlackboxes

private def mixedInnerChildren :
    (name : SileanTests.Fixtures.HierarchicalDualNot.instancePorts.Name) →
      ModuleStructure (SileanTests.Fixtures.HierarchicalDualNot.instancePorts.ports name)
  | .forwardNot => .primitive Primitives.not
  | .backwardNot => .blackbox Primitives.not

private def mixedInner :
    ModuleStructure SileanTests.Fixtures.HierarchicalDualNot.ports :=
  .composite SileanTests.Fixtures.HierarchicalDualNot.body mixedInnerChildren

private def mixedOuterChildren :
    (name : SileanTests.Fixtures.RepeatedDualNot.instancePorts.Name) →
      ModuleStructure (SileanTests.Fixtures.RepeatedDualNot.instancePorts.ports name)
  | .first => SileanTests.Fixtures.HierarchicalDualNot.moduleStructure
  | .second => mixedInner

private def mixedHierarchy :
    ModuleStructure SileanTests.Fixtures.RepeatedDualNot.ports :=
  .composite SileanTests.Fixtures.RepeatedDualNot.body mixedOuterChildren

example : ¬mixedHierarchy.HasNoBlackboxes := by
  decide

#guard !mixedHierarchy.hasNoBlackboxes

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderClosedCircuit Naming.Primitive.not with
  | .ok text => contains text "public module not_bit"
  | .error _ => false

private def blackboxNotNaming :
    Naming.ModuleNaming (ModuleStructure.blackbox Primitives.not) :=
  .blackbox ⟨"blackbox_not", "bit", []⟩ Naming.Primitive.unaryPorts
    Naming.Primitive.emptySignals

#guard match renderClosedCircuit blackboxNotNaming with
  | .ok _ => false
  | .error message => contains message "contains a blackbox"

end SileanTests.ModuleClosure
