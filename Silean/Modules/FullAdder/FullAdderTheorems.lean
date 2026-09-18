import Silean.Modules.FullAdder.Internal.FullAdderVerification

/-! # Full-adder theorems

These are the reader-facing guarantees for the circuit in `FullAdder.lean`.
The statements describe its observable behavior; their proofs use the typed
structure and certification machinery kept under `Internal/`.
-/

namespace Silean.Modules.FullAdder

open Silean

namespace Behavior

/-- A full adder's two output bits encode the natural-number sum of its inputs. -/
theorem numeric_value {inputs : ports.inputs.Values}
    {outputs : ports.outputs.Values} (behavior : Behavior inputs outputs) :
    (outputs .sum).toNat + 2 * (outputs .carryOut).toNat =
      (inputs .left).toNat + (inputs .right).toNat + (inputs .carryIn).toNat := by
  rw [behavior.sum, behavior.carryOut]
  cases inputs .left <;> cases inputs .right <;> cases inputs .carryIn <;> decide

end Behavior

namespace Description

open Naming Authoring.CircuitDescription

/--
Elaborating the circuit description in `FullAdder.lean` produces the typed
structural hierarchy named by `FullAdder.naming`, without name collisions.

This checks the translation from the authoring notation to the structure; the
structure's Boolean behavior is stated separately by `behavior_of_realization`.
-/
theorem authored_definition_corresponds :
    Corresponds description FullAdder.naming :=
  Internal.corresponds

/-- Every realizable boundary step of the structural full adder has the
observable behavior specified in `FullAdder.lean`. Internal wire and child
values are hidden by `Realizes`, making this the reusable structural interface
for downstream proofs. -/
theorem behavior_of_realization {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    Behavior step.inputs step.outputs :=
  FullAdder.Internal.behavior_of_realization realizes

end Description

/-- The concrete full-adder hierarchy contains no behavioral blackboxes. -/
theorem noBlackboxesCertified :
    ModuleStructure.NoBlackboxesCertified moduleStructure :=
  Internal.noBlackboxesCertified

/-- The concrete full-adder structure implements its exact cycle contract at
the shared boundary-step interface. -/
theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

end Silean.Modules.FullAdder
