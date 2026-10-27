import Silean2.CIRCTH
import Silean2.Modules.AddH
import Silean2.Modules.AddWrapperH

namespace Silean2.Modules

open Silean2.CIRCT

def registry : Except String Registry := do
  let r := Registry.empty
  let r ← r.register Add.addName Add.addRegistration
  let r ← r.register
    AddWrapper.AddWrapperFromAdd.addWrapperFromAddName
    AddWrapper.AddWrapperFromAdd.addWrapperFromAddRegistration
  return r

end Silean2.Modules
