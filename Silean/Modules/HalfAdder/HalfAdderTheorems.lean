import Silean.Modules.HalfAdder.Internal.HalfAdderVerification

/-! # Half-adder theorems

These are the reader-facing guarantees for the circuit in `HalfAdder.lean`.
The statements describe the authored circuit and the arithmetic meaning of its
observable behavior; certification details remain under `Internal/`.
-/

namespace Silean.Modules.HalfAdder

open Silean

namespace Behavior

/-- A half adder's two output bits encode the natural-number sum of its inputs. -/
theorem numeric_value {inputs : ports.inputs.Values}
    {outputs : ports.outputs.Values} (behavior : Behavior inputs outputs) :
    (outputs .sum).toNat + 2 * (outputs .carry).toNat =
      (inputs .left).toNat + (inputs .right).toNat := by
  rw [behavior.sum, behavior.carry]
  exact Primitives.xor_toNat_add_twice_and _ _

end Behavior

namespace Description

open Naming Authoring.CircuitDescription

/--
Elaborating the circuit description in `HalfAdder.lean` produces the typed
structural hierarchy named by `HalfAdder.naming`, without name collisions.

This checks the translation from the authoring notation to the structure; the
structure's Boolean behavior is stated separately by `behavior_of_realization`.
-/
theorem authored_definition_corresponds :
    Corresponds description HalfAdder.naming :=
  Internal.corresponds

/-- Every realizable boundary step of the structural half adder has the
observable behavior specified in `HalfAdder.lean`. Internal wire and child
values are hidden by `Realizes`, making this the reusable structural interface
for downstream proofs. -/
theorem behavior_of_realization {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    Behavior step.inputs step.outputs :=
  HalfAdder.Internal.behavior_of_realization realizes

end Description

/-- The concrete half-adder hierarchy contains no behavioral blackboxes. -/
theorem noBlackboxesCertified :
    ModuleStructure.NoBlackboxesCertified moduleStructure :=
  Internal.noBlackboxesCertified

/-- The concrete half-adder structure implements its exact cycle contract at
the shared boundary-step interface. -/
theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

end Silean.Modules.HalfAdder
