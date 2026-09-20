import Silean.Modules.EnabledResetRegister.EnabledResetRegister

assert_not_imported Silean.Modules.EnabledResetRegister.Internal.EnabledResetRegisterStructure
assert_not_imported Silean.Modules.EnabledResetRegister.Internal.EnabledResetRegisterVerification

namespace SileanTests.EnabledResetRegisterAuthoring

open Silean

#check Modules.EnabledResetRegister.cycleContract.value
#check Modules.EnabledResetRegister.next_stored_of_allowed
#check Modules.EnabledResetRegister.next_stored_of_reset
#check Modules.EnabledResetRegister.next_stored_of_enabled
#check Modules.EnabledResetRegister.next_stored_of_disabled
#check ∀ (signalType : SignalType) (resetValue : signalType.Denote),
  (Modules.EnabledResetRegister.description signalType resetValue).ImplementsCycleContract
    (Modules.EnabledResetRegister.cycleContract signalType resetValue)
    (Modules.EnabledResetRegister.Naming.ports signalType)

end SileanTests.EnabledResetRegisterAuthoring
