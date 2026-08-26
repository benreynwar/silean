import Silean2.FIRRTL.PrimitiveNaming
import Silean2.FIRRTL.Render
import Silean2.Modules.BitMux

namespace Silean2.FIRRTL.BitMuxNaming

open Silean2 Silean2.FIRRTL

def ports : ModulePortsNaming Modules.BitMux.ports where
  inputs := ⟨fun
    | .select => "select"
    | .whenFalse => "when_false"
    | .whenTrue => "when_true"⟩
  outputs := ⟨fun | .result => "result"⟩

def instanceName : Modules.BitMux.Instance → SourceName
  | .invertSelect => "invert_select"
  | .chooseFalse => "choose_false"
  | .chooseTrue => "choose_true"
  | .combine => "combine"

def childNaming : (child : Modules.BitMux.Instance) →
    ModuleNaming (Modules.BitMux.childStructure child)
  | .invertSelect => PrimitiveNaming.not
  | .chooseFalse | .chooseTrue => PrimitiveNaming.and
  | .combine => PrimitiveNaming.or

def naming : ModuleNaming Modules.BitMux.moduleStructure := by
  unfold Modules.BitMux.moduleStructure Certified.moduleStructure
  exact .composite ⟨"mux", "bit_gates", []⟩ ports instanceName childNaming

def occurrences : List ModuleOccurrence := collectOccurrences naming
def definitions : List NamedModule := collectDefinitions naming
def instances : List InstanceOccurrence := instanceOccurrences naming
def connections : List (ConnectionOccurrence Modules.BitMux.body) :=
  connectionOccurrences Modules.BitMux.body

def firrtl : RenderResult String := renderCircuit naming

end Silean2.FIRRTL.BitMuxNaming
