import Silean.Modules.ResetRegister.ResetRegister

assert_not_imported Silean.Modules.ResetRegister.Internal.ResetRegisterStructure
assert_not_imported Silean.Modules.ResetRegister.Internal.ResetRegisterVerification

namespace SileanTests.ResetRegisterAuthoring

open Silean

#check Modules.ResetRegister.value_of_allowed
#check Modules.ResetRegister.next_stored_of_allowed
#check ∀ (signalType : SignalType) (resetValue : signalType.Denote),
  (Modules.ResetRegister.description signalType resetValue).ImplementsCycleContract
    (Modules.ResetRegister.cycleContract signalType resetValue)
    (Modules.ResetRegister.Naming.ports signalType)

end SileanTests.ResetRegisterAuthoring
