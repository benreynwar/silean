import Silean.Authoring.ModuleWiring
import Silean.Authoring.ModuleChildCertifications
import Silean.Modules.HalfAdder.HalfAdderTheorems
import Silean.Primitives.Or

namespace Silean.Examples.Checks.ModuleWiringAuthoring

open Silean Silean.Authoring

module_ports ports where
  input left : .bit,
  input right : .bit,
  output result : .bit

module_instances instancePorts for ports where
  adder := Modules.HalfAdder.moduleStructure,
  combine := ModuleStructure.primitive Primitives.or

private def adderRightSource :
    SignalSource context.ports context.instancePorts .bit :=
  context.moduleInput .right

module_wiring wiring for context where
  outputs {
    .result := combine.output }
  instance (.adder) {
    .left := input.left,
    .right := from (adderRightSource) }
  instance (.combine) {
    .left := adder.sum,
    .right := adder.carry }

module_child_certifications childContracts for body where
  adder := Modules.HalfAdder.certification,
  combine := Primitives.orCertified.certification

example : body.wiring.moduleOutput .result =
    context.instanceOutput .combine .output := rfl

example : body.wiring.instanceInput .adder .right =
    context.moduleInput .right := rfl

example : moduleStructure = .composite body structuralChildren := rfl

example : childContracts .adder = Modules.HalfAdder.cycleContract := rfl

example (child : instancePorts.Name) :
    (certifiedChildren child).moduleStructure = structuralChildren child :=
  certifiedChildren_moduleStructure child

end Silean.Examples.Checks.ModuleWiringAuthoring

namespace Silean.Examples.Checks.ModuleWiringAuthoring.Indexed

open Silean Silean.Authoring

module_ports ports (count : Nat) where
  input value : .bit,
  output value : .bit

module_instances instancePorts (count : Nat) for ports count where
  gates (index : Fin count in Enumeration.fin count)
    (name := s!"gate_{index.val}") := ModuleStructure.primitive Primitives.or,
  combine := ModuleStructure.primitive Primitives.or

module_wiring wiring (count : Nat) for context count where
  outputs {
    .value := combine.output }
  instance (.gates index) {
    .left := input.value,
    .right := gates(index)[.output] }
  instance (.combine) {
    .left := input.value,
    .right := input.value }

module_child_certifications childContracts (count : Nat) for body count where
  gates (_index : Fin count) := Primitives.orCertified.certification,
  combine := Primitives.orCertified.certification

example (count : Nat) (index : Fin count) :
    (body count).wiring.instanceInput (.gates index) .left =
      (context count).moduleInput .value := rfl

example (count : Nat) (index : Fin count) :
    childContracts count (.gates index) = Primitives.orCycleContract := rfl

example (count : Nat) (child : (instancePorts count).Name) :
    (certifiedChildren count child).moduleStructure =
      structuralChildren count child :=
  certifiedChildren_moduleStructure count child

end Silean.Examples.Checks.ModuleWiringAuthoring.Indexed
