import Silean2.Foundation.SignalMap

namespace Silean2

/-! A module boundary contains connectivity only; state belongs to structure. -/

structure ModuleSignature where
  inputs : List SignalType
  outputs : List SignalType

structure ModulePorts where
  inputs : SignalMap
  outputs : SignalMap

def ModulePorts.signature (ports : ModulePorts) : ModuleSignature where
  inputs := ports.inputs.types
  outputs := ports.outputs.types

end Silean2
