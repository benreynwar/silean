import Silean2.FIRRTL.MuxNaming
import Silean2.FIRRTL.RegisterNaming
import Silean2.Modules.EnabledRegister

namespace Silean2.FIRRTL.EnabledRegisterNaming

open Silean2 Silean2.FIRRTL

def portsWithNaming (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.EnabledRegister.ports signalType) where
  inputs := ⟨fun | .value => "value" | .enable => "enable"⟩
  outputs := ⟨fun | .value => "value_out"⟩
  inputTypes := fun | .value => typeNaming | .enable => .bit
  outputTypes := fun | .value => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.EnabledRegister.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.EnabledRegister.moduleStructure signalType) := by
  unfold Modules.EnabledRegister.moduleStructure
  exact .composite ⟨"enabled_register", "structural", [.shape signalType]⟩
    (portsWithNaming signalType typeNaming)
    (fun | .selection => "selection" | .storage => "storage")
    (fun | .selection => MuxNaming.namingWith signalType typeNaming
         | .storage => RegisterNaming.namingWith signalType typeNaming)

def naming (signalType : SignalType) :
    ModuleNaming (Modules.EnabledRegister.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

def firrtl (signalType : SignalType) : RenderResult String :=
  renderCircuit (naming signalType)

end Silean2.FIRRTL.EnabledRegisterNaming
