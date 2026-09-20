import Silean.Modules.OneEntryFifo.OneEntryFifo

assert_not_imported Silean.Modules.OneEntryFifo.Internal.OneEntryFifoStructure
assert_not_imported Silean.Modules.OneEntryFifo.Internal.OneEntryFifoVerification
assert_not_imported Silean.Modules.OneEntryFifo.Internal.OneEntryFifoFifoVerification

namespace SileanTests.OneEntryFifoAuthoring

open Silean

#check (Modules.OneEntryFifo.description .bit).ImplementsCycleContract
  (Modules.OneEntryFifo.cycleContract .bit)
  (Naming.FifoPorts.ports .bit)

end SileanTests.OneEntryFifoAuthoring
