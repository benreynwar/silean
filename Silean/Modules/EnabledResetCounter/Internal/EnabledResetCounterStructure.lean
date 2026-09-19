import Silean.Authoring.ModuleDesign
import Silean.Modules.EnabledResetRegister.EnabledResetRegister
import Silean.Modules.Increment.Increment

/-! The expanded typed hierarchy for `EnabledResetCounter`.

The reader-facing feedback circuit and its contract live in
`EnabledResetCounter.lean`; this file supplies the representation required by
structural verification and emission.
-/

namespace Silean.Modules.EnabledResetCounter

open Silean
open Silean.Authoring

abbrev Value (width : Nat) := Fin width → Bool

@[reducible] def valueType (width : Nat) : SignalType :=
  .vector width .bit

module_ports ports (width : Nat)
    with (typeNaming : Silean.Naming.SignalTypeNaming (valueType width) :=
      .positional (valueType width)) where
  input enable : .bit,
  input reset : .bit,
  output value (schema := typeNaming) : valueType width

end Silean.Modules.EnabledResetCounter

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design EnabledResetCounter (width : Nat)
    (resetValue : EnabledResetCounter.Value width)
    (specialization := .natural width ::
      Constant.Naming.parameters (EnabledResetCounter.valueType width) resetValue)
    with (typeNaming : Silean.Naming.SignalTypeNaming
      (EnabledResetCounter.valueType width) :=
        .positional (EnabledResetCounter.valueType width)) where
  boundary (EnabledResetCounter.ports width)
    (naming := EnabledResetCounter.Naming.ports width)
    (namingWith := EnabledResetCounter.Naming.portsWithNaming width typeNaming)
  instances {
    increment (name := .indexed "increment" 0) := Increment.design width,
    storage (name := .indexed "enabled_reset_register" 0) :=
      EnabledResetRegister.design
      (EnabledResetCounter.valueType width) resetValue }
  named_wires {
    current := storage.value }
  wiring {
    outputs {
      .value := storage.value }
    instance (.increment) {
      .value := storage.value }
    instance (.storage) {
      .value := increment.result,
      .enable := input.enable,
      .reset := input.reset }
  }

end Silean.Modules

namespace Silean.Modules.EnabledResetCounter.Internal

open Silean

@[simp] theorem increment_instance_name (width : Nat)
    (resetValue : Value width) :
    EnabledResetCounter.Naming.instanceNames width resetValue .increment =
      .indexed "increment" 0 := rfl

@[simp] theorem storage_instance_name (width : Nat)
    (resetValue : Value width) :
    EnabledResetCounter.Naming.instanceNames width resetValue .storage =
      .indexed "enabled_reset_register" 0 := rfl

@[simp] theorem increment_child_ports (width : Nat)
    (resetValue : Value width) :
    ((EnabledResetCounter.body width resetValue).instancePorts.ports
      .increment) = Increment.ports width := rfl

@[simp] theorem storage_child_ports (width : Nat)
    (resetValue : Value width) :
    ((EnabledResetCounter.body width resetValue).instancePorts.ports
      .storage) = EnabledResetRegister.ports (valueType width) := rfl

end Silean.Modules.EnabledResetCounter.Internal
