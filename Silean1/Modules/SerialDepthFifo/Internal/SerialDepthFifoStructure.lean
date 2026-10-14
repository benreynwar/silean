import Silean.Composition.FifoSerialComposition
import Silean.Modules.OneEntryFifo.OneEntryFifoDerived
import Silean.Modules.SerialDepthFifo.SerialDepthFifo

/-! Recursive structural expansion for positive-depth serial FIFOs. -/

namespace Silean.Modules.SerialDepthFifo.Internal

open Silean

def moduleStructureFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) →
      ModuleStructure (Silean.Interfaces.Fifo.ports signalType)
  | 0 => OneEntryFifo.moduleStructure signalType
  | additionalDepth + 1 =>
      Composition.FifoSerial.moduleStructure signalType
        (OneEntryFifo.moduleStructure signalType)
        (moduleStructureFromAdditional signalType additionalDepth)

end Silean.Modules.SerialDepthFifo.Internal

namespace Silean.Modules.SerialDepthFifo

open Silean

def moduleStructure (signalType : SignalType)
    (depth : Nat) (_positive : 0 < depth) :
    ModuleStructure (Silean.Interfaces.Fifo.ports signalType) :=
  Internal.moduleStructureFromAdditional signalType (additionalDepth depth)

end Silean.Modules.SerialDepthFifo
