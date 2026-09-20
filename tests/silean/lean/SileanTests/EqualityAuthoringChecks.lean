import Silean.Modules.Equality.Equality

assert_not_imported Silean.Modules.Equality.Internal.EqualityStructure
assert_not_imported Silean.Modules.Equality.Internal.EqualityVerification

namespace SileanTests.EqualityAuthoring

open Silean

#check Modules.Equality.cycleContract
#check Modules.Equality.cycleContract.result

end SileanTests.EqualityAuthoring
