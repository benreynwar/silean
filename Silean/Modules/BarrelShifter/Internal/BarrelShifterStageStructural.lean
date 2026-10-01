import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.BarrelShifter.Internal.BarrelShifterStageStructure

/-! Contract-independent certification of one aligned pipeline stage. -/

namespace Silean.Modules.BarrelShifter.Internal.Stage

open Silean
open Silean.Authoring
open Silean.Modules

private abbrev wholeRules (element : SignalType) (exponent : Nat)
    (stage : Fin exponent) (registerInput : Bool) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (BarrelShifterStage.body element exponent stage registerInput)

module_complete_schedule completeSchedule
    (element : SignalType) (exponent : Nat) (stage : Fin exponent)
    (registerInput : Bool)
    for BarrelShifterStage.body element exponent stage registerInput
    with wholeRules element exponent stage registerInput := [
  .dataDelay => .apply,
  .shiftDelay => .apply,
  .level => .apply]

private theorem childStructuralCertifications
    (element : SignalType) (exponent : Nat) (stage : Fin exponent)
    (registerInput : Bool) :
    ∀ child,
      ModuleStructuralCertification
        (BarrelShifterStage.structuralChildren
          element exponent stage registerInput child)
  | .dataDelay => OptionalShiftRegister.structuralCertification
      (.vector (size exponent) element) registerInput.toNat
  | .shiftDelay => OptionalShiftRegister.structuralCertification
      (.vector exponent .bit) registerInput.toNat
  | .level => Level.structuralCertification element exponent stage

/-- One aligned stage has a unique structural solution. -/
theorem structuralCertification (element : SignalType) (exponent : Nat)
    (stage : Fin exponent) (registerInput : Bool) :
    ModuleStructuralCertification
      (BarrelShifterStage.moduleStructure
        element exponent stage registerInput) :=
  (completeSchedule element exponent stage registerInput).certifyComposite
    (BarrelShifterStage.structuralChildren
      element exponent stage registerInput)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (BarrelShifterStage.body element exponent stage registerInput)
      (BarrelShifterStage.structuralChildren
        element exponent stage registerInput)
      (childStructuralCertifications
        element exponent stage registerInput))
    (fun _ => rfl)

end Silean.Modules.BarrelShifter.Internal.Stage
