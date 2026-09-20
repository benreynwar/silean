import Silean.Modules.Register.Register

assert_not_imported Silean.Modules.Register.Internal.RegisterStructure
assert_not_imported Silean.Modules.Register.Internal.RegisterVerification

namespace SileanTests.RegisterAuthoring

open Silean

#check Modules.Register.output_of_allowed
#check Modules.Register.next_stored_of_allowed

end SileanTests.RegisterAuthoring
