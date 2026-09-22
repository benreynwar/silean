import Silean.Authoring.ModuleDesign
import Silean.Modules.OptionalShiftRegister.OptionalShiftRegister
import Silean.Modules.Register.RegisterDerived

/-! Shared register-chain structure for the positive and optional modules. -/

namespace Silean.Modules

open Silean
open Silean.Authoring

/- Internal generated declarations.  The public `ShiftRegister` facade adds
the positivity requirement; `OptionalShiftRegister` deliberately exposes the
zero-stage specialization of this same structure. -/
module_design ShiftRegisterImplementation
    (signalType : SignalType) (latency : Nat) (name := "ShiftRegister") where
  boundary (ShiftRegister.ports signalType)
    (naming := ShiftRegister.Naming.ports signalType)
  instances {
    delay (stage : Fin latency in Enumeration.fin latency)
      (name := .indexed "register" stage.val) := Register.design signalType }
  wiring {
    outputs {
      .output := from (
        if zero : latency = 0 then
          (ShiftRegisterImplementation.context signalType latency)
            |>.moduleInput .input
        else
          (ShiftRegisterImplementation.context signalType latency)
            |>.instanceOutput (.delay ⟨latency - 1, by omega⟩) .output) }
    instance (.delay stage) {
      .input := from (
        if first : stage.val = 0 then
          (ShiftRegisterImplementation.context signalType latency)
            |>.moduleInput .input
        else
          (ShiftRegisterImplementation.context signalType latency)
            |>.instanceOutput (.delay ⟨stage.val - 1, by omega⟩) .output) }
  }

namespace ShiftRegister

abbrev moduleStructure (signalType : SignalType) (latency : Nat)
    (_positive : 0 < latency) :=
  ShiftRegisterImplementation.moduleStructure signalType latency

def naming (signalType : SignalType) (latency : Nat)
    (_positive : 0 < latency) :
    Naming.ModuleNaming (moduleStructure signalType latency _positive) :=
  ShiftRegisterImplementation.naming signalType latency

def design (signalType : SignalType) (latency : Nat)
    (positive : 0 < latency) : Naming.NamedModule where
  ports := ports signalType
  moduleStructure := moduleStructure signalType latency positive
  naming := naming signalType latency positive

end ShiftRegister

namespace OptionalShiftRegister

abbrev moduleStructure (signalType : SignalType) (latency : Nat) :=
  ShiftRegisterImplementation.moduleStructure signalType latency

def naming (signalType : SignalType) (latency : Nat) :
    Naming.ModuleNaming (moduleStructure signalType latency) :=
  (ShiftRegisterImplementation.naming signalType latency).withKey {
    family := "OptionalShiftRegister"
    variant := ""
    specialization :=
      [Naming.ModuleParameter.of signalType,
       Naming.ModuleParameter.of latency] }

def design (signalType : SignalType) (latency : Nat) :
    Naming.NamedModule where
  ports := ports signalType
  moduleStructure := moduleStructure signalType latency
  naming := naming signalType latency

end OptionalShiftRegister

end Silean.Modules
