import Silean.Examples.Fixtures.RepeatedDualNot
import Silean.FIRRTL
import Silean.Naming.ModuleNaming
import Silean.Naming.PrimitiveNaming

namespace Silean.Examples.Checks.ModuleClosure

open Silean Silean.FIRRTL

example : (ModuleStructure.primitive Primitives.not).HasNoBlackboxes := by
  decide

example : Examples.Fixtures.RepeatedDualNot.moduleStructure.HasNoBlackboxes := by
  decide

#guard Examples.Fixtures.RepeatedDualNot.moduleStructure.hasNoBlackboxes

example : ¬(ModuleStructure.blackbox Primitives.not).HasNoBlackboxes := by
  decide

#guard !(ModuleStructure.blackbox Primitives.not).hasNoBlackboxes

private def mixedInnerChildren :
    (name : Examples.Fixtures.HierarchicalDualNot.instancePorts.Name) →
      ModuleStructure (Examples.Fixtures.HierarchicalDualNot.instancePorts.ports name)
  | .forwardNot => .primitive Primitives.not
  | .backwardNot => .blackbox Primitives.not

private def mixedInner :
    ModuleStructure Examples.Fixtures.HierarchicalDualNot.ports :=
  .composite Examples.Fixtures.HierarchicalDualNot.body mixedInnerChildren

private def mixedOuterChildren :
    (name : Examples.Fixtures.RepeatedDualNot.instancePorts.Name) →
      ModuleStructure (Examples.Fixtures.RepeatedDualNot.instancePorts.ports name)
  | .first => Examples.Fixtures.HierarchicalDualNot.moduleStructure
  | .second => mixedInner

private def mixedHierarchy :
    ModuleStructure Examples.Fixtures.RepeatedDualNot.ports :=
  .composite Examples.Fixtures.RepeatedDualNot.body mixedOuterChildren

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

end Silean.Examples.Checks.ModuleClosure
