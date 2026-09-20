import Silean.Modules.OneEntryFifo.Control.OneEntryFifoControl

assert_not_imported Silean.Modules.OneEntryFifo.Control.Internal.OneEntryFifoControlStructure
assert_not_imported Silean.Modules.OneEntryFifo.Control.Internal.OneEntryFifoControlVerification

namespace SileanTests.OneEntryFifoControlAuthoring

open Silean

#check Modules.OneEntryFifo.Control.description.ImplementsCycleContract
  Modules.OneEntryFifo.Control.cycleContract
  Modules.OneEntryFifo.Control.Naming.ports

end SileanTests.OneEntryFifoControlAuthoring
