import Silean.Foundation.ModulePorts

namespace Silean

/-! # One module cycle at its boundary

`CycleStep` collects the four values visible at a module boundary during one
cycle. It deliberately says nothing about whether those values are allowed by
a behavioral contract or realizable by a hardware structure. Those are
separate relations defined by the contract and structural semantics layers.

Internal wires, child outputs, and structural equation assignments do not
belong here: two different implementations of the same behavior should still
describe the same boundary step.
-/

/-- Inputs and state before an edge, together with outputs and state after it. -/
structure CycleStep (ports : ModulePorts) (State : Type) where
  inputs : ports.inputs.Values
  currentState : State
  outputs : ports.outputs.Values
  nextState : State

end Silean
