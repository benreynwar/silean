import Silean2.FIRRTL.LogicNaming
import Silean2.FIRRTL.Render
import Silean2.Modules.Mux

namespace Silean2.FIRRTL.MuxNaming

open Silean2 Silean2.FIRRTL

def portsWithNaming (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.Mux.ports signalType) where
  inputs := ⟨fun
    | .select => "select"
    | .whenFalse => "when_false"
    | .whenTrue => "when_true"⟩
  outputs := ⟨fun | .result => "result"⟩
  inputTypes := fun
    | .select => .bit
    | .whenFalse | .whenTrue => typeNaming
  outputTypes := fun | .result => typeNaming

def ports (signalType : SignalType) : ModulePortsNaming (Modules.Mux.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.Mux.moduleStructure signalType) := by
  unfold Modules.Mux.moduleStructure
  exact .composite ⟨"mux", "structural", [.shape signalType]⟩
    (portsWithNaming signalType typeNaming)
    (fun
      | .invertSelect => "invert_select"
      | .chooseFalse => "choose_false"
      | .chooseTrue => "choose_true"
      | .combine => "combine")
    (fun
      | .invertSelect => PrimitiveNaming.not
      | .chooseFalse | .chooseTrue => MaskNaming.namingWith signalType typeNaming
      | .combine => BitwiseOrNaming.namingWith signalType typeNaming)

def naming (signalType : SignalType) :
    ModuleNaming (Modules.Mux.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

def firrtl (signalType : SignalType) : RenderResult String :=
  renderCircuit (naming signalType)

end Silean2.FIRRTL.MuxNaming
