import Silean.Modules.EnabledResetCounter.EnabledResetCounter

assert_not_imported Silean.Modules.EnabledResetCounter.Internal.EnabledResetCounterStructure
assert_not_imported Silean.Modules.EnabledResetCounter.Internal.EnabledResetCounterVerification

namespace SileanTests.EnabledResetCounterAuthoring

open Silean

#check Modules.EnabledResetCounter.value_of_allowed
#check Modules.EnabledResetCounter.next_stored_of_allowed
#check Modules.EnabledResetCounter.next_stored_of_reset
#check Modules.EnabledResetCounter.next_stored_of_enabled
#check Modules.EnabledResetCounter.next_stored_of_disabled
#check Modules.EnabledResetCounter.next_toNat_of_enabled
#check ∀ (width : Nat) (resetValue : Modules.EnabledResetCounter.Value width),
  (Modules.EnabledResetCounter.description width resetValue).ImplementsCycleContract
    (Modules.EnabledResetCounter.cycleContract width resetValue)
    (Modules.EnabledResetCounter.Naming.ports width)

end SileanTests.EnabledResetCounterAuthoring
