import Silean.Modules.FullAdder.FullAdder

assert_not_imported Silean.Modules.FullAdder.Internal.FullAdderStructure
assert_not_imported Silean.Modules.FullAdder.Internal.FullAdderVerification

namespace SileanTests.FullAdderAuthoring

open Silean

#check Modules.FullAdder.description.ImplementsCycleContract
  Modules.FullAdder.cycleContract Modules.FullAdder.Naming.ports

end SileanTests.FullAdderAuthoring
