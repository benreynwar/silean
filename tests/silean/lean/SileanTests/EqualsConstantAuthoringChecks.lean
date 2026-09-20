import Silean.Modules.EqualsConstant.EqualsConstant

assert_not_imported Silean.Modules.EqualsConstant.Internal.EqualsConstantStructure
assert_not_imported Silean.Modules.EqualsConstant.Internal.EqualsConstantVerification

namespace SileanTests.EqualsConstantAuthoring

open Silean

#check (Modules.EqualsConstant.description .bit false).ImplementsCycleContract
  (Modules.EqualsConstant.cycleContract .bit false)
  (Modules.EqualsConstant.Naming.ports .bit)

end SileanTests.EqualsConstantAuthoring
