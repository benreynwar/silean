import PicoRV.Alu
import PicoRV.Regs
import PicoRV.Memory.MemoryLookahead

assert_not_imported PicoRV.Internal.AluStructure
assert_not_imported PicoRV.Internal.AluVerification
assert_not_imported PicoRV.Internal.RegsStructure
assert_not_imported PicoRV.Internal.RegsVerification
assert_not_imported PicoRV.Memory.Internal.MemoryLookaheadStructure
assert_not_imported PicoRV.Memory.Internal.MemoryLookaheadVerification

namespace PicoRVTests.ClientAuthoring

#check PicoRV.Alu.description.ImplementsCycleContract
  PicoRV.Alu.cycleContract PicoRV.Alu.Naming.ports

#check PicoRV.Regs.description.ImplementsCycleContract
  PicoRV.Regs.cycleContract PicoRV.Regs.Naming.ports

#check PicoRV.Memory.Lookahead.description.ImplementsCycleContract
  PicoRV.Memory.Lookahead.cycleContract PicoRV.Memory.Lookahead.Naming.ports

end PicoRVTests.ClientAuthoring
