import PicoRV.PicoRVSchedule
import Silean.FIRRTL

namespace PicoRVTests.Top

open Silean Silean.Contracts.Cycle.Certification

/-! Focused compile-time checks for the configured top-level composition.
These exercise the real `ModuleStructure` and its schedules; the older
boundary audit checks the source inventory independently. -/

example (output : PicoRV.PicoRV.Output) :
    Silean.Contracts.Cycle.Certification.Layer.sourceAvailable (fun _ : PicoRV.PicoRV.Input => True)
      (PicoRV.PicoRV.outputSchedule output).finalAvailability
      (PicoRV.PicoRV.body.wiring.moduleOutput output) :=
  (PicoRV.PicoRV.outputSchedule output).finished

example : PicoRV.PicoRV.moduleStructure.HasAtMostOneSolution :=
  PicoRV.PicoRV.hasAtMostOneSolution

example : PicoRV.PicoRV.moduleStructure.HasSolution :=
  PicoRV.PicoRV.hasSolution

example : PicoRV.PicoRV.moduleStructure.HasExactlyOneSolution :=
  PicoRV.PicoRV.hasExactlyOneSolution

example : PicoRV.PicoRV.moduleStructure.HasNoBlackboxes :=
  PicoRV.PicoRV.moduleStructure_hasNoBlackboxes

example : PicoRV.PicoRV.structuralChildren .control =
    PicoRV.Control.moduleStructure := rfl

example : PicoRV.PicoRV.structuralChildren .datapath =
    PicoRV.Datapath.moduleStructure := rfl

example : PicoRV.PicoRV.structuralChildren .mem =
    PicoRV.Memory.moduleStructure := rfl

example : PicoRV.PicoRV.structuralChildren .decoder =
    PicoRV.Decoder.moduleStructure := rfl

example : PicoRV.PicoRV.structuralChildren .cpuregs =
    PicoRV.Regs.moduleStructure := rfl

/-! ## Recursive closure inventory -/

def expectedTopChildClosed : PicoRV.PicoRV.Instance → Bool
  | _ => true

example (child : PicoRV.PicoRV.Instance) :
    (PicoRV.PicoRV.structuralChildren child).hasNoBlackboxes =
      expectedTopChildClosed child := by
  cases child <;> native_decide

example :
    (PicoRV.Decoder.structuralChildren .capture).hasNoBlackboxes = true := by
  native_decide

example :
    (PicoRV.Decoder.structuralChildren .resolve).hasNoBlackboxes = true := by
  native_decide

def expectedResolveChildClosed :
    PicoRV.Decoder.ResolveStage.Instance → Bool
  | _ => true

example (child : PicoRV.Decoder.ResolveStage.Instance) :
    (PicoRV.Decoder.ResolveStage.structuralChildren child).hasNoBlackboxes =
      expectedResolveChildClosed child := by
  cases child <;> native_decide

example :
    PicoRV.Decoder.ResolveStage.structuralChildren .instructionMatch =
      PicoRV.Decoder.InstructionMatch.Structure.moduleStructure := rfl

example :
    PicoRV.Decoder.ResolveStage.structuralChildren .instructionSummary =
      PicoRV.Decoder.InstructionSummary.Structure.moduleStructure := rfl

#guard match Silean.FIRRTL.renderCircuit PicoRV.PicoRV.naming with
  | .ok _ => true
  | .error _ => false

#guard match Silean.FIRRTL.renderClosedCircuit PicoRV.PicoRV.naming with
  | .ok _ => true
  | .error _ => false

end PicoRVTests.Top
