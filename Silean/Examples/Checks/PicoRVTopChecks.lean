import Silean.Examples.PicoRV.PicoRVSchedule

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

example : Layer.ChildrenStateInputsReady Silean.Examples.PicoRV.PicoRV.body
    Silean.Examples.PicoRV.PicoRV.childContracts
    Silean.Examples.PicoRV.PicoRV.stateSchedule.finalAvailability :=
  Silean.Examples.PicoRV.PicoRV.stateSchedule.finished

example : Layer.CoversAllRules Silean.Examples.PicoRV.PicoRV.body
    Silean.Examples.PicoRV.PicoRV.childContracts
    Silean.Examples.PicoRV.PicoRV.allRulesSchedule.finalAvailability :=
  Silean.Examples.PicoRV.PicoRV.allRulesSchedule.finished

example : Silean.Examples.PicoRV.PicoRV.moduleStructure.HasAtMostOneSolution :=
  Silean.Examples.PicoRV.PicoRV.hasAtMostOneSolution

example : ¬Silean.Examples.PicoRV.PicoRV.moduleStructure.HasNoBlackboxes := by
  intro closed
  exact ModuleStructure.not_hasNoBlackboxes_blackbox _ (closed.child .control)

example : (Silean.Examples.PicoRV.PicoRV.children .control).moduleStructure =
    Silean.Examples.PicoRV.Control.cycleContract.blackboxStructure := rfl

example : (Silean.Examples.PicoRV.PicoRV.children .datapath).moduleStructure =
    Silean.Examples.PicoRV.Datapath.cycleContract.blackboxStructure := rfl

example : (Silean.Examples.PicoRV.PicoRV.children .mem).moduleStructure =
    Silean.Examples.PicoRV.Memory.cycleContract.blackboxStructure := rfl

example : (Silean.Examples.PicoRV.PicoRV.children .decoder).moduleStructure =
    Silean.Examples.PicoRV.Decoder.cycleContract.blackboxStructure := rfl

example : (Silean.Examples.PicoRV.PicoRV.children .cpuregs).moduleStructure =
    Silean.Examples.PicoRV.Regs.cycleContract.blackboxStructure := rfl

end Silean.Examples.Checks.PicoRVTop
