import Silean.Modules.EnabledRegister.EnabledRegister

assert_not_imported Silean.Modules.EnabledRegister.Internal.EnabledRegisterStructure
assert_not_imported Silean.Modules.EnabledRegister.Internal.EnabledRegisterVerification

namespace SileanTests.EnabledRegisterAuthoring

open Silean

#check Modules.EnabledRegister.cycleContract.q
#check Modules.EnabledRegister.next_stored_of_allowed
#check Modules.EnabledRegister.next_stored_of_enabled
#check Modules.EnabledRegister.next_stored_of_disabled
#check ∀ (signalType : SignalType),
  (Modules.EnabledRegister.description signalType).ImplementsCycleContract
    (Modules.EnabledRegister.cycleContract signalType)
    (Modules.EnabledRegister.Naming.ports signalType)

end SileanTests.EnabledRegisterAuthoring
