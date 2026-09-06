import Silean.Authoring.ModuleDesign
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.Mux.Mux
import Silean.Modules.Register.Register

namespace Silean.Modules

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

/-! ## Hardware structure -/

/- A register which loads `data` when `enable` is high and otherwise retains
its current value. -/
module_design EnabledRegister (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  ports {
    input data (schema := typeNaming) : signalType,
    input enable : .bit,
    output q (schema := typeNaming) : signalType }
  instances {
    -- Chooses between the new input and the stored value.
    selection := Modules.Mux.design signalType,
    -- Holds the selected value across cycles.
    storage := Modules.Register.design signalType }
  wiring {
    outputs {
      -- The stored value is exposed directly.
      .q := storage.output }
    -- Select the new input when enabled, or feed the stored value back.
    instance (.selection) {
      .select := input.enable,
      .whenFalse := storage.output,
      .whenTrue := input.data }
    -- Store the mux result on the next clock edge.
    instance (.storage) {
      .input := selection.result }
  }

end Silean.Modules

namespace Silean.Modules.EnabledRegister
open Silean
/-! ## Exact cycle behavior -/

module_cycle_contract cycleContract (signalType : SignalType)
    for ports signalType where
  state := Modules.Register.stateMap signalType
  output_rule observe where
    reads := []
    writes := { q := state .stored }
  state_rule where
    reads := [enable, data]
    next := { stored := bif enable then data else state .stored }
end Silean.Modules.EnabledRegister
