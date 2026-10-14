import Silean.Foundation.ModulePorts

namespace Silean

/-! # One observable module cycle

`BoundaryStep` records only the values visible at a module boundary during one
cycle. It deliberately omits implementation and contract state, so sequences
of boundary steps can be used as natural, implementation-independent
behavioral specifications.
-/

/-- The externally visible input and output values for one module cycle. -/
structure BoundaryStep (ports : ModulePorts) where
  inputs : ports.inputs.Values
  outputs : ports.outputs.Values

end Silean
