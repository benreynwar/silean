import Silean.Authoring.ModuleDesign
import Silean.Modules.BarrelShifter.Internal.BarrelShifterStageVerification
import Silean.Modules.OptionalShiftRegister.OptionalShiftRegisterDerived

/-! # Structural barrel-shifter hierarchy

There is one aligned pipeline stage per shift bit.  Each stage contains the
optional data/control register pair at its input and its conditional
power-of-two rotation.  One final optional register supplies the output
boundary.
-/

namespace Silean.Modules.BarrelShifter.Internal

open Silean

/-- Previous pipeline stage (used only on the noninitial wiring branch). -/
def previousStage (exponent : Nat) (stage : Fin exponent) : Fin exponent :=
  ⟨stage.val - 1, by omega⟩

/-- Last pipeline stage when the shift word is nonempty. -/
def lastStage (exponent : Nat) (nonempty : exponent ≠ 0) : Fin exponent :=
  ⟨exponent - 1, Nat.sub_lt (Nat.zero_lt_of_ne_zero nonempty) Nat.zero_lt_one⟩

/-- Stage immediately before a nonzero stage boundary. -/
def stageBeforeBoundary (exponent : Nat) (boundary : Fin (exponent + 1))
    (nonzero : boundary.val ≠ 0) : Fin exponent :=
  ⟨boundary.val - 1, by omega⟩

@[simp] theorem stageBeforeBoundary_succ (stage : Fin exponent) :
    stageBeforeBoundary exponent stage.succ (by simp) = stage := by
  apply Fin.ext
  simp [stageBeforeBoundary]

theorem stageBeforeBoundary_castSucc (stage : Fin exponent)
    (nonzero : stage.val ≠ 0) :
    stageBeforeBoundary exponent stage.castSucc nonzero =
      previousStage exponent stage := by
  apply Fin.ext
  rfl

theorem stageBeforeBoundary_final (nonempty : exponent ≠ 0) :
    stageBeforeBoundary exponent (Fin.last exponent) nonempty =
      lastStage exponent nonempty := by
  apply Fin.ext
  rfl

/-- Stable emission identity for the element type, geometry, and complete
optional-register placement. -/
def specialization (element : SignalType) (exponent : Nat)
    (pipeline : Pipeline exponent) : List Naming.ModuleParameter :=
  [.signalType element, .natural exponent] ++
    (List.finRange (exponent + 1)).map fun boundary =>
      .boolean (pipeline.registerBoundary boundary)

end Silean.Modules.BarrelShifter.Internal

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design BarrelShifter (element : SignalType) (exponent : Nat)
    (pipeline : BarrelShifter.Pipeline exponent)
    (specialization :=
      BarrelShifter.Internal.specialization element exponent pipeline) where
  boundary (BarrelShifter.ports element exponent)
    (naming := BarrelShifter.Naming.ports element exponent)
  instances {
    stage
        (stage : Fin exponent in Enumeration.fin exponent)
        (name := .indexed "stage" stage.val) :=
      BarrelShifterStage.design element exponent stage
        (pipeline.registerBoundary stage.castSucc),
    outputDelay := OptionalShiftRegister.design
      (.vector (BarrelShifter.size exponent) element)
      (pipeline.registerBoundary (Fin.last exponent)).toNat }
  wiring {
    outputs {
      .result := outputDelay.output }
    instance (.stage stage) {
      .shift := from (
        let context := BarrelShifter.context element exponent pipeline
        if _zero : stage.val = 0 then
          context.moduleInput .shift
        else
          context.instanceOutput
            (.stage (BarrelShifter.Internal.previousStage exponent stage))
            .shift),
      .data := from (
        let context := BarrelShifter.context element exponent pipeline
        if _zero : stage.val = 0 then
          context.moduleInput .data
        else
          context.instanceOutput
            (.stage (BarrelShifter.Internal.previousStage exponent stage))
            .result) }
    instance (.outputDelay) {
      .input := from (
        let context := BarrelShifter.context element exponent pipeline
        if empty : exponent = 0 then
          context.moduleInput .data
        else
          context.instanceOutput
            (.stage (BarrelShifter.Internal.lastStage exponent empty))
            .result) }
  }

end Silean.Modules
