import Silean.Authoring.ModuleDesign
import Silean.Interfaces.FifoPorts
import Silean.Modules.EnabledResetCounter.EnabledResetCounterDerived
import Silean.Modules.Fifo.Internal.FifoPointerControlStructure
import Silean.Modules.Fifo.Fifo
import Silean.Modules.RegisterBank.RegisterBankDerived
import Silean.Naming.FifoPortsNaming

/-! Expanded typed structure for the reader-facing register-bank FIFO. -/

namespace Silean.Modules

open Silean
open Silean.Authoring
open Silean.Interfaces.Fifo

module_design Fifo (element : SignalType) (addressWidth : Nat) where
  boundary (Interfaces.Fifo.ports element)
    (naming := Naming.FifoPorts.ports element)
  instances {
    -- Tracks the entry currently presented at the output.
    readCounter :=
      EnabledResetCounter.design (addressWidth + 1)
        (Fifo.zeroPointer addressWidth),
    -- Tracks the entry where the next accepted input will be stored.
    writeCounter :=
      EnabledResetCounter.design (addressWidth + 1)
        (Fifo.zeroPointer addressWidth),
    -- Derives handshake decisions and storage addresses from the pointers.
    control (name := .indexed "fifo_pointer_control" 0) :=
      Fifo.PointerControl.design addressWidth,
    -- Holds all FIFO data entries and provides the asynchronous read port.
    storage (name := .indexed "register_bank" 0) :=
      RegisterBank.design element addressWidth 1 }
  named_wires {
    readAdvance := control.readAdvance,
    writeAdvance := control.writeAdvance }
  wiring {
    outputs {
      .outputValid := control.outputValid,
      .outputData := storage[.readValue 0],
      .inputReady := control.inputReady }
    instance (.readCounter) {
      .enable := control.readAdvance,
      .reset := input.reset }
    instance (.writeCounter) {
      .enable := control.writeAdvance,
      .reset := input.reset }
    instance (.control) {
      .readPointer := readCounter.value,
      .writePointer := writeCounter.value,
      .inputValid := input.inputValid,
      .outputReady := input.outputReady }
    instance (.storage) {
      .writeEnable := control.writeAdvance,
      .writeAddress := control.writeAddress,
      .writeValue := input.inputData,
      .readAddress 0 := control.readAddress }
  }

namespace Fifo.Internal

open Silean.Naming

def namingWith (element : SignalType) (addressWidth : Nat)
    (elementNaming : SignalTypeNaming element) :
    ModuleNaming (Fifo.moduleStructure element addressWidth) := by
  unfold Fifo.moduleStructure
  exact .composite
    ⟨"Fifo", "", [.signalType element, .natural addressWidth]⟩
    (Silean.Naming.FifoPorts.portsWithNaming element elementNaming)
    (Fifo.Naming.instanceNames element addressWidth)
    (fun
      | .readCounter => EnabledResetCounter.naming (addressWidth + 1)
          (Fifo.zeroPointer addressWidth)
      | .writeCounter => EnabledResetCounter.naming (addressWidth + 1)
          (Fifo.zeroPointer addressWidth)
      | .control => Fifo.PointerControl.naming addressWidth
      | .storage => RegisterBank.Naming.namingWith element addressWidth 1
          elementNaming)

end Fifo.Internal

end Silean.Modules
