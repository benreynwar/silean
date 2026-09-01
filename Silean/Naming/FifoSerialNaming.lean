import Silean.Composition.FifoSerialComposition
import Silean.Naming.FifoPortsNaming

namespace Silean.Composition.FifoSerial.Naming

open Silean Silean.Naming

/-! Naming for the generic serial FIFO composition lives above Composition:
the structural construction itself has no dependency on presentation names. -/

def serialNamingWith (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) (depth : Nat)
    {upstream downstream : ModuleStructure (Silean.Interfaces.Fifo.ports signalType)}
    (upstreamNaming : ModuleNaming upstream)
    (downstreamNaming : ModuleNaming downstream) :
    ModuleNaming (Composition.FifoSerial.moduleStructure signalType upstream downstream) := by
  unfold Composition.FifoSerial.moduleStructure
  exact .composite
    ⟨"serial_depth_fifo", "structural", [.shape signalType, .natural depth]⟩
    (Silean.Naming.FifoPorts.portsWithNaming signalType typeNaming)
    (fun | .upstream => "upstream" | .downstream => "downstream")
    (fun | .upstream => upstreamNaming | .downstream => downstreamNaming)

end Silean.Composition.FifoSerial.Naming
