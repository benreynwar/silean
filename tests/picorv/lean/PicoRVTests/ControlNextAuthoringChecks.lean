import PicoRV.Control.ControlNext

assert_not_imported PicoRV.Control.Internal.ControlNextStructure
assert_not_imported PicoRV.Control.Internal.ControlNextVerification

namespace PicoRVTests.ControlNextAuthoring

#check PicoRV.Control.ControlNext.cycleContract

#check PicoRV.Control.ControlNext.description.ImplementsCycleContract
  PicoRV.Control.ControlNext.cycleContract
  PicoRV.Control.ControlNext.Naming.ports

end PicoRVTests.ControlNextAuthoring
