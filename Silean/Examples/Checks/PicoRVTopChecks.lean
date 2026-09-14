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

example : Silean.Examples.PicoRV.PicoRV.moduleStructure.HasSolution :=
  Silean.Examples.PicoRV.PicoRV.hasSolution

example : Silean.Examples.PicoRV.PicoRV.moduleStructure.HasExactlyOneSolution :=
  Silean.Examples.PicoRV.PicoRV.hasExactlyOneSolution

example : Silean.Examples.PicoRV.PicoRV.moduleStructure.HasNoBlackboxes :=
  Silean.Examples.PicoRV.PicoRV.moduleStructure_hasNoBlackboxes

example : Silean.Examples.PicoRV.PicoRV.structuralChildren .control =
    Silean.Examples.PicoRV.Control.moduleStructure := rfl

example : Silean.Examples.PicoRV.PicoRV.structuralChildren .datapath =
    Silean.Examples.PicoRV.Datapath.moduleStructure := rfl

example : Silean.Examples.PicoRV.PicoRV.structuralChildren .mem =
    Silean.Examples.PicoRV.Memory.moduleStructure := rfl

example : Silean.Examples.PicoRV.PicoRV.structuralChildren .decoder =
    Silean.Examples.PicoRV.Decoder.moduleStructure := rfl

example : Silean.Examples.PicoRV.PicoRV.structuralChildren .cpuregs =
    Silean.Examples.PicoRV.Regs.moduleStructure := rfl

/-! ## Recursive closure inventory -/

def expectedTopChildClosed : Silean.Examples.PicoRV.PicoRV.Instance → Bool
  | _ => true

example (child : Silean.Examples.PicoRV.PicoRV.Instance) :
    (Silean.Examples.PicoRV.PicoRV.structuralChildren child).hasNoBlackboxes =
      expectedTopChildClosed child := by
  cases child <;> native_decide

example :
    (Silean.Examples.PicoRV.Decoder.structuralChildren .capture).hasNoBlackboxes = true := by
  native_decide

example :
    (Silean.Examples.PicoRV.Decoder.structuralChildren .resolve).hasNoBlackboxes = true := by
  native_decide

def expectedResolveChildClosed :
    Silean.Examples.PicoRV.Decoder.ResolveStage.Instance → Bool
  | _ => true

example (child : Silean.Examples.PicoRV.Decoder.ResolveStage.Instance) :
    (Silean.Examples.PicoRV.Decoder.ResolveStage.structuralChildren child).hasNoBlackboxes =
      expectedResolveChildClosed child := by
  cases child <;> native_decide

example :
    Silean.Examples.PicoRV.Decoder.ResolveStage.structuralChildren .instructionMatch =
      Silean.Examples.PicoRV.Decoder.InstructionMatch.Structure.moduleStructure := rfl

example :
    Silean.Examples.PicoRV.Decoder.ResolveStage.structuralChildren .instructionSummary =
      Silean.Examples.PicoRV.Decoder.InstructionSummary.Structure.moduleStructure := rfl

#guard match Silean.FIRRTL.renderCircuit Silean.Examples.PicoRV.PicoRV.naming with
  | .ok _ => true
  | .error _ => false

#guard match Silean.FIRRTL.renderClosedCircuit Silean.Examples.PicoRV.PicoRV.naming with
  | .ok _ => true
  | .error _ => false

end Silean.Examples.Checks.PicoRVTop
