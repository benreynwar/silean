import Silean.Foundation.BoundaryStep

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

namespace CycleStep

/-- Erase the state transition from a cycle, retaining its observable module
boundary values. -/
def boundary (step : CycleStep ports State) : BoundaryStep ports where
  inputs := step.inputs
  outputs := step.outputs

@[simp] theorem boundary_inputs (step : CycleStep ports State) :
    step.boundary.inputs = step.inputs :=
  rfl

@[simp] theorem boundary_outputs (step : CycleStep ports State) :
    step.boundary.outputs = step.outputs :=
  rfl

end CycleStep

end Silean
