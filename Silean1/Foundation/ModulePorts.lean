import Silean.Foundation.SignalMap

namespace Silean

/-! A module boundary contains connectivity only; state belongs to structure. -/

structure ModulePorts where
  inputs : SignalMap
  outputs : SignalMap

end Silean
