import Silean.Modules.Fifo.Fifo

assert_not_imported Silean.Modules.Fifo.Internal.FifoStructure
assert_not_imported Silean.Modules.Fifo.Internal.FifoCycleVerification
assert_not_imported Silean.Modules.Fifo.Internal.FifoCorrespondence
assert_not_imported Silean.Modules.Fifo.Internal.FifoFifoVerification
assert_not_imported Silean.Modules.Fifo.Internal.FifoPropertiesVerification

namespace SileanTests.FifoAuthoring

open Silean

#check (Modules.Fifo.description .bit 2).ImplementsCycleContract
  (Modules.Fifo.cycleContract .bit 2)
  (Naming.FifoPorts.ports .bit)

end SileanTests.FifoAuthoring
