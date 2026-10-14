import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.BarrelShifter.Internal.BarrelShifterLevel
import Silean.Modules.Mux.MuxDerived
import Silean.Modules.VectorReindex.VectorReindexDerived
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.BarrelShifter.Internal.Level

open Silean

def shiftSplitter (exponent : Nat) : Composition.SignalSplitter :=
  .vector exponent .bit

/-- Stable emission identity for a particular logarithmic mux level. -/
def specialization (element : SignalType) (exponent : Nat)
    (stage : Fin exponent) : List Naming.ModuleParameter :=
  [.signalType element, .natural exponent, .natural stage.val]

end Silean.Modules.BarrelShifter.Internal.Level

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design BarrelShifterLevel (element : SignalType) (exponent : Nat)
    (stage : Fin exponent) (variant := s!"stage_{stage.val}")
    (specialization :=
      BarrelShifter.Internal.Level.specialization element exponent stage) where
  boundary (BarrelShifter.Internal.Level.ports element exponent)
    (naming := BarrelShifter.Internal.Level.Naming.ports element exponent)
  instances {
    shiftSplit := Naming.SignalAdapter.splitterDesign
      (BarrelShifter.Internal.Level.shiftSplitter exponent),
    rotate := VectorReindex.design element (BarrelShifter.size exponent)
      (BarrelShifter.size exponent)
      (BarrelShifter.Internal.Level.sourceIndex exponent stage),
    select := Mux.design (.vector (BarrelShifter.size exponent) element) }
  wiring {
    outputs {
      .result := select.result }
    instance (.shiftSplit) {
      .value := input.shift }
    instance (.rotate) {
      .input := input.data }
    instance (.select) {
      .select := shiftSplit[stage],
      .whenFalse := input.data,
      .whenTrue := rotate.output }
  }

end Silean.Modules
