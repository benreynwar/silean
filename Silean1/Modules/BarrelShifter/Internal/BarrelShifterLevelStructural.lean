import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.BarrelShifter.Internal.BarrelShifterLevelStructure

/-! Contract-independent structural certification for one mux level. -/

namespace Silean.Modules.BarrelShifter.Internal.Level

open Silean
open Silean.Authoring
open Silean.Modules

private abbrev wholeRules (element : SignalType) (exponent : Nat)
    (stage : Fin exponent) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (BarrelShifterLevel.body element exponent stage)

module_complete_schedule completeSchedule
    (element : SignalType) (exponent : Nat) (stage : Fin exponent)
    for BarrelShifterLevel.body element exponent stage
    with wholeRules element exponent stage := [
  .shiftSplit => .apply,
  .rotate => .apply,
  .select => .apply]

private theorem childStructuralCertifications
    (element : SignalType) (exponent : Nat) (stage : Fin exponent) :
    ∀ child,
      ModuleStructuralCertification
        (BarrelShifterLevel.structuralChildren element exponent stage child)
  | .shiftSplit => (shiftSplitter exponent).structuralCertification
  | .rotate =>
      (VectorReindex.certification element (BarrelShifter.size exponent)
        (BarrelShifter.size exponent) (sourceIndex exponent stage)).structural
  | .select =>
      (Mux.certification (.vector (BarrelShifter.size exponent) element)).structural

/-- One logarithmic mux level has a unique structural solution. -/
theorem structuralCertification (element : SignalType) (exponent : Nat)
    (stage : Fin exponent) :
    ModuleStructuralCertification
      (BarrelShifterLevel.moduleStructure element exponent stage) :=
  (completeSchedule element exponent stage).certifyComposite
    (BarrelShifterLevel.structuralChildren element exponent stage)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (BarrelShifterLevel.body element exponent stage)
      (BarrelShifterLevel.structuralChildren element exponent stage)
      (childStructuralCertifications element exponent stage))
    (fun _ => rfl)

end Silean.Modules.BarrelShifter.Internal.Level
