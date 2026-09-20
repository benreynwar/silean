import Silean.Authoring.ModuleInstances
import Silean.Modules.HalfAdder.HalfAdderDerived
import Silean.Modules.Mux.Mux
import Silean.Modules.Register.RegisterDerived
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.OrPrimitive

namespace SileanTests.ModuleInstancesAuthoring

open Silean Silean.Authoring

module_ports ports where
  input left : .bit,
  input right : .bit,
  output result : .bit

module_instances instancePorts for ports where
  adder := Modules.HalfAdder.moduleStructure,
  combine (name := "combine_result") := ModuleStructure.primitive Primitives.or

example : instancePorts.ports .adder = Modules.HalfAdder.ports := rfl
example : structuralChildren .adder = Modules.HalfAdder.moduleStructure := rfl
example : Naming.instanceNames .combine = "combine_result" := rfl

end SileanTests.ModuleInstancesAuthoring

namespace SileanTests.ModuleInstancesAuthoring.GenericStateful

open Silean Silean.Authoring

module_ports ports (signalType : SignalType) where
  input value : signalType,
  output value : signalType

module_instances instancePorts (signalType : SignalType)
    for ports signalType where
  selection := Modules.Mux.moduleStructure signalType,
  storage := Modules.Register.moduleStructure signalType

example (signalType : SignalType) :
    (instancePorts signalType).ports .selection = Modules.Mux.ports signalType := rfl

example (signalType : SignalType) :
    structuralChildren signalType .storage =
      Modules.Register.moduleStructure signalType := rfl

end SileanTests.ModuleInstancesAuthoring.GenericStateful

namespace SileanTests.ModuleInstancesAuthoring.Indexed

open Silean Silean.Authoring

module_ports ports (count : Nat) where
  input value : .bit,
  output value : .bit

module_instances instancePorts (count : Nat) for ports count where
  first := ModuleStructure.primitive Primitives.or,
  adders (index : Fin count in Enumeration.fin count)
    (name := s!"adder_{index.val}") := Modules.HalfAdder.moduleStructure,
  last := ModuleStructure.primitive Primitives.or

example :
    (instancePorts 2).keys.values =
      [.first, .adders 0, .adders 1, .last] := rfl

example (count : Nat) (index : Fin count) :
    (instancePorts count).ports (.adders index) = Modules.HalfAdder.ports := rfl

example (count : Nat) (index : Fin count) :
    structuralChildren count (.adders index) = Modules.HalfAdder.moduleStructure := rfl

example (count : Nat) (index : Fin count) :
    Naming.instanceNames count (.adders index) = s!"adder_{index.val}" := rfl

end SileanTests.ModuleInstancesAuthoring.Indexed
