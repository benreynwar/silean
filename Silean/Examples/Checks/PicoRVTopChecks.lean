import Silean.Examples.PicoRV.PicoRVSchedule
import Silean.FIRRTL

namespace Silean.Examples.Checks.PicoRVTop

open Silean Silean.Contracts.Cycle.Certification

/-! Focused compile-time checks for the configured top-level composition.
These exercise the real `ModuleStructure` and its schedules; the older
boundary audit checks the source inventory independently. -/

example (output : Silean.Examples.PicoRV.PicoRV.Output) :
    Layer.sourceAvailable (fun _ : Silean.Examples.PicoRV.PicoRV.Input => True)
      (Silean.Examples.PicoRV.PicoRV.outputSchedule output).finalAvailability
      (Silean.Examples.PicoRV.PicoRV.body.wiring.moduleOutput output) :=
  (Silean.Examples.PicoRV.PicoRV.outputSchedule output).finished

example : Silean.Examples.PicoRV.PicoRV.moduleStructure.HasAtMostOneSolution :=
  Silean.Examples.PicoRV.PicoRV.hasAtMostOneSolution

example : ¬Silean.Examples.PicoRV.PicoRV.moduleStructure.HasNoBlackboxes := by
  intro closed
  exact ModuleStructure.not_hasNoBlackboxes_blackbox _ (closed.child .control)

example : Silean.Examples.PicoRV.PicoRV.structuralChildren .control =
    Silean.Examples.PicoRV.Control.cycleContract.blackboxStructure := rfl

example : Silean.Examples.PicoRV.PicoRV.structuralChildren .datapath =
    Silean.Examples.PicoRV.Datapath.cycleContract.blackboxStructure := rfl

example : Silean.Examples.PicoRV.PicoRV.structuralChildren .mem =
    Silean.Examples.PicoRV.Memory.cycleContract.blackboxStructure := rfl

example : Silean.Examples.PicoRV.PicoRV.structuralChildren .decoder =
    Silean.Examples.PicoRV.Decoder.cycleContract.blackboxStructure := rfl

example : Silean.Examples.PicoRV.PicoRV.structuralChildren .cpuregs =
    Silean.Examples.PicoRV.Regs.cycleContract.blackboxStructure := rfl

-- The open hierarchy emits its five intentional blackboxes as external
-- modules, but closed emission must reject the same boundary.
#guard match Silean.FIRRTL.renderCircuit Silean.Examples.PicoRV.PicoRV.naming with
  | .ok _ => true
  | .error _ => false

#guard match Silean.FIRRTL.renderClosedCircuit Silean.Examples.PicoRV.PicoRV.naming with
  | .ok _ => false
  | .error _ => true

end Silean.Examples.Checks.PicoRVTop
