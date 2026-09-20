import Silean.Modules.HalfAdder.HalfAdder

assert_not_imported Silean.Modules.HalfAdder.Internal.HalfAdderStructure
assert_not_imported Silean.Modules.HalfAdder.Internal.HalfAdderVerification

namespace SileanTests.HalfAdderAuthoring

open Silean

#check Modules.HalfAdder.description.ImplementsCycleContract
  Modules.HalfAdder.cycleContract Modules.HalfAdder.Naming.ports

end SileanTests.HalfAdderAuthoring
