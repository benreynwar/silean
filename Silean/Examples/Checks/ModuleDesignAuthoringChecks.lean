import Silean.Authoring.ModuleDesign
import Silean.Naming.PrimitiveNaming

namespace Silean.Examples.Checks.ModuleDesignAuthoring

open Silean Silean.Authoring

module_design DefaultNames where
  ports {
    input left : .bit,
    input right : .bit,
    output result : .bit }
  instances {
    combine := Primitives.orDesign }
  wiring {
    outputs {
      .result := combine.output }
    instance (.combine) {
      .left := input.left,
      .right := input.right }
  }

example : DefaultNames.design.key.family = "DefaultNames" := rfl
example : DefaultNames.design.key.variant = "" := rfl
example : DefaultNames.Naming.ports.inputs.name .left = "left" := rfl
example : DefaultNames.Naming.instanceNames .combine = "combine" := rfl
example : DefaultNames.structuralChildren .combine =
    Primitives.orDesign.moduleStructure := rfl
example : DefaultNames.body.wiring.instanceInput .combine .right =
    DefaultNames.context.moduleInput .right := rfl

module_design ExistingBoundary where
  boundary (Silean.Examples.Checks.ModuleDesignAuthoring.DefaultNames.ports)
    (naming := Silean.Examples.Checks.ModuleDesignAuthoring.DefaultNames.Naming.ports)
  instances {
    combine := Primitives.orDesign }
  wiring {
    outputs {
      .result := combine.output }
    instance (.combine) {
      .left := input.left,
      .right := input.right }
  }

example : ExistingBoundary.design.ports = DefaultNames.ports := rfl
example : ExistingBoundary.Naming.instanceNames .combine = "combine" := rfl

module_design OverriddenNames (name := "customModule") (variant := "example")
    (specialization := [.natural 3]) where
  ports {
    input value (name := "customInput") : .bit,
    output result : .bit }
  instances {
    invert (name := "customInstance") := Primitives.notDesign }
  wiring {
    outputs {
      .result := invert.output }
    instance (.invert) {
      .input := input.value }
  }

example : OverriddenNames.design.key.family = "customModule" := rfl
example : OverriddenNames.design.key.variant = "example" := rfl
example : OverriddenNames.design.key.specialization = [.natural 3] := rfl
example : OverriddenNames.Naming.ports.inputs.name .value = "customInput" := rfl
example : OverriddenNames.Naming.instanceNames .invert = "customInstance" := rfl

module_design IndexedChildren (count : Nat) where
  ports {
    input value : .bit,
    output result : .bit }
  instances {
    outputDriver := Primitives.notDesign,
    workers (index : Fin count in Enumeration.fin count)
      (name := s!"worker_{index.val}") := Primitives.notDesign }
  wiring {
    outputs {
      .result := outputDriver.output }
    instance (.outputDriver) {
      .input := input.value }
    instance (.workers _index) {
      .input := input.value }
  }

example : (IndexedChildren.design 2).key.family = "IndexedChildren" := rfl
example : (IndexedChildren.design 2).key.specialization = [.natural 2] := rfl
example : (IndexedChildren.Naming.instanceNames 2 (.workers 1)) =
    "worker_1" := rfl
example : IndexedChildren.structuralChildren 2 (.workers 0) =
    Primitives.notDesign.moduleStructure := rfl
example : (IndexedChildren.instancePorts 2).names.values =
    [.outputDriver, .workers 0, .workers 1] := rfl
example : (IndexedChildren.body 2).wiring.instanceInput (.workers 1) .input =
    (IndexedChildren.context 2).moduleInput .value := rfl

end Silean.Examples.Checks.ModuleDesignAuthoring
