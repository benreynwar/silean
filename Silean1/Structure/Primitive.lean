import Silean.Foundation.DeriveEnumeration
import Silean.Foundation.ModulePorts
import Silean.Foundation.StructuralState

namespace Silean

/-! The generic description of a primitive leaf. Its ports and local state may
use any signal shapes; the current concrete primitives under
`Silean.Primitives` choose single-bit interfaces as a library convention. The
foundation does not contain a closed list of primitives. -/

structure Primitive where
  /-- The primitive's external input and output signals. -/
  ports : ModulePorts
  /-- State stored by the primitive. -/
  localState : SignalMap
  /-- Inputs on which the outputs may depend. -/
  outputReads : List ports.inputs.Label
  /-- The primitive's outputs for given inputs and state. -/
  outputValues : ports.inputs.Values → localState.Values → ports.outputs.Values
  /-- The primitive's state after the next clock edge. -/
  nextStateValues : ports.inputs.Values → localState.Values → localState.Values
  /-- Proof that inputs omitted from `outputReads` cannot affect the
  outputs, making the declared combinational dependencies sound. -/
  outputRespectsReads : ∀ left right currentState,
    (∀ input, input ∈ outputReads → left input = right input) →
      outputValues left currentState = outputValues right currentState

end Silean
