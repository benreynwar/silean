import Silean2.DeriveEnumeration
import Silean2.Foundation.ModulePorts
import Silean2.Foundation.StructuralState

namespace Silean2

/-! The generic description of a single-bit primitive leaf. Concrete
primitives are independent values under `Silean2.Primitives`; the foundation
does not contain a closed list of them. -/

structure Primitive where
  ports : ModulePorts
  localState : SignalMap
  outputReads : List ports.inputs.Label
  outputValues : ports.inputs.Values → localState.Values → ports.outputs.Values
  nextStateValues : ports.inputs.Values → localState.Values → localState.Values
  outputRespectsReads : ∀ left right currentState,
    (∀ input, input ∈ outputReads → left input = right input) →
      outputValues left currentState = outputValues right currentState

end Silean2
