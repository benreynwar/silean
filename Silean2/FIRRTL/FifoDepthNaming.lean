import Silean2.FIRRTL.FifoNaming
import Silean2.Modules.Fifo

namespace Silean2.FIRRTL.FifoNaming

open Silean2

def serialNamingWith (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) (depth : Nat)
    {upstream downstream : ModuleStructure (Modules.OneEntryFifo.ports signalType)}
    (upstreamNaming : ModuleNaming upstream)
    (downstreamNaming : ModuleNaming downstream) :
    ModuleNaming (Modules.SerialFifo.moduleStructure signalType upstream downstream) := by
  unfold Modules.SerialFifo.moduleStructure
  exact .composite
    ⟨"fifo", "structural", [.shape signalType, .natural depth]⟩
    (OneEntryFifoNaming.portsWithNaming signalType typeNaming)
    (fun | .upstream => "upstream" | .downstream => "downstream")
    (fun | .upstream => upstreamNaming | .downstream => downstreamNaming)

def namingFromAdditional (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    (additionalDepth : Nat) →
      ModuleNaming (Modules.Fifo.moduleStructureFromAdditional signalType additionalDepth)
  | 0 => OneEntryFifoNaming.namingWith signalType typeNaming
  | additionalDepth + 1 =>
      serialNamingWith signalType typeNaming (additionalDepth + 2)
        (OneEntryFifoNaming.namingWith signalType typeNaming)
        (namingFromAdditional signalType typeNaming additionalDepth)

def depthNamingWith (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType)
    (depth : Nat) (positive : 0 < depth) :
    ModuleNaming (Modules.Fifo.moduleStructure signalType depth positive) :=
  namingFromAdditional signalType typeNaming (Modules.Fifo.additionalDepth depth)

def depthNaming (signalType : SignalType) (depth : Nat) (positive : 0 < depth) :
    ModuleNaming (Modules.Fifo.moduleStructure signalType depth positive) :=
  depthNamingWith signalType (.positional signalType) depth positive

def depthFirrtl (signalType : SignalType) (depth : Nat)
    (positive : 0 < depth) : RenderResult String :=
  renderCircuit (depthNaming signalType depth positive)

end Silean2.FIRRTL.FifoNaming
