import Silean.Authoring.ModuleDesign
import Silean.Modules.BarrelShifter.Internal.BarrelShifterLevelVerification
import Silean.Modules.BarrelShifter.Internal.BarrelShifterStage
import Silean.Modules.OptionalShiftRegister.OptionalShiftRegisterDerived

namespace Silean.Modules.BarrelShifter.Internal.Stage

open Silean

def specialization (element : SignalType) (exponent : Nat)
    (stage : Fin exponent) (registerInput : Bool) :
    List Naming.ModuleParameter :=
  [.signalType element, .natural exponent, .natural stage.val,
   .boolean registerInput]

end Silean.Modules.BarrelShifter.Internal.Stage

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design BarrelShifterStage (element : SignalType) (exponent : Nat)
    (stage : Fin exponent) (registerInput : Bool)
    (variant := s!"stage_{stage.val}")
    (specialization := BarrelShifter.Internal.Stage.specialization
      element exponent stage registerInput) where
  boundary (BarrelShifter.Internal.Stage.ports element exponent)
    (naming := BarrelShifter.Internal.Stage.Naming.ports element exponent)
  instances {
    dataDelay := OptionalShiftRegister.design
      (.vector (BarrelShifter.size exponent) element) registerInput.toNat,
    shiftDelay := OptionalShiftRegister.design
      (.vector exponent .bit) registerInput.toNat,
    level := BarrelShifterLevel.design element exponent stage }
  wiring {
    outputs {
      .shift := shiftDelay.output,
      .result := level.result }
    instance (.dataDelay) {
      .input := input.data }
    instance (.shiftDelay) {
      .input := input.shift }
    instance (.level) {
      .shift := shiftDelay.output,
      .data := dataDelay.output }
  }

end Silean.Modules
