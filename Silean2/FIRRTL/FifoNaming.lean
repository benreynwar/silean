import Silean2.FIRRTL.EnabledRegisterNaming
import Silean2.Modules.OneEntryFifo

namespace Silean2.FIRRTL

open Silean2

namespace FifoControlNaming

def ports : ModulePortsNaming Modules.FifoControl.ports where
  inputs := ⟨fun | .storedValid => "stored_valid" | .downstreamReady => "downstream_ready"⟩
  outputs := ⟨fun | .upstreamReady => "upstream_ready" | .storageUpdate => "storage_update"⟩

def naming : ModuleNaming Modules.FifoControl.moduleStructure := by
  unfold Modules.FifoControl.moduleStructure Certified.moduleStructure
  exact .composite ⟨"fifo_control", "structural", []⟩ ports
    (fun | .invertValid => "invert_valid" | .readyOr => "ready_or" | .updateEq => "update_eq")
    (fun | .invertValid => PrimitiveNaming.not
         | .readyOr => PrimitiveNaming.or
         | .updateEq => PrimitiveNaming.eq)

end FifoControlNaming

namespace OneEntryFifoNaming

def portsWithNaming (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.OneEntryFifo.ports signalType) where
  inputs := ⟨fun
    | .inputValid => "input_valid"
    | .inputData => "input_data"
    | .outputReady => "output_ready"⟩
  outputs := ⟨fun
    | .outputValid => "output_valid"
    | .outputData => "output_data"
    | .inputReady => "input_ready"⟩
  inputTypes := fun
    | .inputValid | .outputReady => .bit
    | .inputData => typeNaming
  outputTypes := fun
    | .outputValid | .inputReady => .bit
    | .outputData => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.OneEntryFifo.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.OneEntryFifo.moduleStructure signalType) := by
  unfold Modules.OneEntryFifo.moduleStructure
  exact .composite ⟨"one_entry_fifo", "structural", [.shape signalType]⟩
    (portsWithNaming signalType typeNaming)
    (fun
      | .validStorage => "valid_storage"
      | .dataStorage => "data_storage"
      | .control => "control"
      | .outputValidOr => "output_valid_or"
      | .outputDataMux => "output_data_mux")
    (fun
      | .validStorage => EnabledRegisterNaming.naming .bit
      | .dataStorage => EnabledRegisterNaming.namingWith signalType typeNaming
      | .control => FifoControlNaming.naming
      | .outputValidOr => PrimitiveNaming.or
      | .outputDataMux => MuxNaming.namingWith signalType typeNaming)

def naming (signalType : SignalType) :
    ModuleNaming (Modules.OneEntryFifo.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

def firrtl (signalType : SignalType) : RenderResult String :=
  renderCircuit (naming signalType)

end OneEntryFifoNaming

end Silean2.FIRRTL
