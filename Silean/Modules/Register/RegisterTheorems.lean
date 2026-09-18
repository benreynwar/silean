import Silean.Modules.Register.Internal.RegisterVerification

/-! # Generic-register theorems

These are the public behavioral and certification results for the recursively
assembled register. The schedules, component-state relation, and induction
that construct the certificate remain under `Internal/`.
-/

namespace Silean.Modules.Register

open Silean

/-! ## Contract equation -/

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (stateMap signalType).Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .output = state .stored := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

/-! ## Public cycle laws -/

section AllowedStep

variable {signalType : SignalType}
  {step : (cycleContract signalType).Step}
  (allowed : (cycleContract signalType).Allows step)

include allowed

/-- A register exposes the value stored before the clock edge. -/
theorem output_of_allowed :
    step.outputs .output = step.currentState .stored :=
  (outputRule_holds_iff signalType
    step.inputs step.currentState step.outputs).mp (allowed.1 .observe)

/-- On the clock edge, a register stores its input. -/
theorem next_stored_of_allowed :
    step.nextState .stored = step.inputs .input := by
  rw [allowed.2]
  rfl

end AllowedStep

/-- The recursively assembled register implements its cycle contract at the
shared boundary-step interface. -/
theorem implements_contract (signalType : SignalType) :
    Contracts.Cycle.Implements
      (moduleStructure signalType)
      (cycleContract signalType)
      (certification signalType).stateCorresponds :=

    (certification signalType).implements

theorem certified_moduleStructure (signalType : SignalType) :
    (certified signalType).moduleStructure = moduleStructure signalType :=
  rfl

end Silean.Modules.Register
