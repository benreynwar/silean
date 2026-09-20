import Silean.Modules.CombMuxTree.CombMuxTree

assert_not_imported Silean.Modules.CombMuxTree.Internal.CombMuxTreeStructure
assert_not_imported Silean.Modules.CombMuxTree.Internal.CombMuxTreeVerification

namespace SileanTests.CombMuxTreeAuthoring

open Silean

#check Modules.CombMuxTree.cycleContract
#check Modules.CombMuxTree.cycleContract.result

end SileanTests.CombMuxTreeAuthoring
