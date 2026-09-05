import Silean.Composition.FifoSerialComposition
import Silean.Naming.FifoPortsNaming

namespace Silean.Composition.FifoSerial.Naming

open Silean Silean.Naming

/-! Naming stays above the generic composition layer so structural and proof
machinery do not depend on presentation metadata. -/

/-- Attach authored payload names and child naming trees to the generic serial
FIFO layer. -/
def serialNamingWith (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) (depth : Nat)
    {upstream downstream : ModuleStructure (Silean.Interfaces.Fifo.ports signalType)}
    (upstreamNaming : ModuleNaming upstream)
    (downstreamNaming : ModuleNaming downstream) :
    ModuleNaming (Composition.FifoSerial.moduleStructure signalType upstream downstream) := by
  unfold Composition.FifoSerial.moduleStructure
  exact .composite
    ⟨"serial_depth_fifo", "structural", [.signalType signalType, .natural depth]⟩
    (Silean.Naming.FifoPorts.portsWithNaming signalType typeNaming)
    (fun | .upstream => "upstream" | .downstream => "downstream")
    (fun | .upstream => upstreamNaming | .downstream => downstreamNaming)

end Silean.Composition.FifoSerial.Naming
