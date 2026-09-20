import Silean.Authoring.ModuleDesign
import Silean.Interfaces.FifoPorts
import Silean.Modules.EnabledRegister.EnabledRegisterDerived
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterDerived
import Silean.Modules.Mux.Mux
import Silean.Modules.OneEntryFifo.Control.OneEntryFifoControl
import Silean.Naming.FifoPortsNaming
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.OrPrimitive

/-! Expanded typed hierarchy for `OneEntryFifo`.

The readable feedback circuit and exact contract live in `OneEntryFifo.lean`.
-/

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design OneEntryFifo (signalType : SignalType) where
  boundary (Interfaces.Fifo.ports signalType)
    (naming := Naming.FifoPorts.ports signalType)
  instances {
    validStorage := EnabledResetRegister.design .bit false,
    dataStorage := EnabledRegister.design signalType,
    control (name := .indexed "one_entry_fifo_control" 0) :=
      OneEntryFifo.Control.design,
    outputValidOr (name := .indexed "or" 0) := Primitives.orDesign,
    outputDataMux (name := .indexed "mux" 0) := Mux.design signalType }
  named_wires {
    storedValid := validStorage.value,
    storedData := dataStorage.q,
    storageUpdate := control.storageUpdate }
  wiring {
    outputs {
      .outputValid := outputValidOr.output,
      .outputData := outputDataMux.result,
      .inputReady := control.upstreamReady }
    instance (.validStorage) {
      .enable := control.storageUpdate,
      .value := input.inputValid,
      .reset := input.reset }
    instance (.dataStorage) {
      .enable := control.storageUpdate,
      .data := input.inputData }
    instance (.control) {
      .storedValid := validStorage.value,
      .downstreamReady := input.outputReady }
    instance (.outputValidOr) {
      .left := validStorage.value,
      .right := input.inputValid }
    instance (.outputDataMux) {
      .select := validStorage.value,
      .whenFalse := input.inputData,
      .whenTrue := dataStorage.q }
  }

end Silean.Modules

namespace Silean.Modules.OneEntryFifo.Internal

@[simp] theorem validStorage_instance_name (signalType : SignalType) :
    OneEntryFifo.Naming.instanceNames signalType .validStorage =
      "validStorage" := rfl

@[simp] theorem dataStorage_instance_name (signalType : SignalType) :
    OneEntryFifo.Naming.instanceNames signalType .dataStorage =
      "dataStorage" := rfl

@[simp] theorem control_instance_name (signalType : SignalType) :
    OneEntryFifo.Naming.instanceNames signalType .control =
      .indexed "one_entry_fifo_control" 0 := rfl

@[simp] theorem outputValidOr_instance_name (signalType : SignalType) :
    OneEntryFifo.Naming.instanceNames signalType .outputValidOr =
      .indexed "or" 0 := rfl

@[simp] theorem outputDataMux_instance_name (signalType : SignalType) :
    OneEntryFifo.Naming.instanceNames signalType .outputDataMux =
      .indexed "mux" 0 := rfl

end Silean.Modules.OneEntryFifo.Internal
