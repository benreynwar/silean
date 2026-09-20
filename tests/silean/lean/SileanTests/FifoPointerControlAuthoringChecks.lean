import Silean.Modules.Fifo.FifoPointerControl

assert_not_imported Silean.Modules.Fifo.Internal.FifoPointerControlStructure
assert_not_imported Silean.Modules.Fifo.Internal.FifoPointerControlVerification
assert_not_imported Silean.Modules.Fifo.Internal.FifoPointerControlCorrespondence

namespace SileanTests.FifoPointerControlAuthoring

open Silean

#check (Modules.Fifo.PointerControl.description 2).ImplementsCycleContract
  (Modules.Fifo.PointerControl.cycleContract 2)
  (Modules.Fifo.PointerControl.Naming.ports 2)

end SileanTests.FifoPointerControlAuthoring
