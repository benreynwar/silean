import Silean.FIRRTL
import Silean.Modules.OptionalShiftRegister.OptionalShiftRegisterDerived
import Silean.Modules.ShiftRegister.ShiftRegisterDerived

namespace SileanTests.ShiftRegisterChecks

open Silean Silean.FIRRTL

example (signalType : SignalType) (latency : Nat) (positive : 0 < latency) :
    ModuleStructuralRuleCertification
      (Modules.ShiftRegister.moduleStructure signalType latency positive)
      (Modules.ShiftRegister.rules signalType latency positive) :=
  Modules.ShiftRegister.certification signalType latency positive

example (signalType : SignalType) (latency : Nat) :
    ModuleStructuralRuleCertification
      (Modules.OptionalShiftRegister.moduleStructure signalType latency)
      (Modules.OptionalShiftRegister.rules signalType latency) :=
  Modules.OptionalShiftRegister.certification signalType latency

example (signalType : SignalType) (latency : Nat)
    {initialState finalState :
      (Modules.OptionalShiftRegister.moduleStructure signalType latency).State}
    {inputs : List
      (Modules.OptionalShiftRegister.ports signalType).inputs.Values}
    {outputs : List
      (Modules.OptionalShiftRegister.ports signalType).outputs.Values}
    (execution :
      (Modules.OptionalShiftRegister.moduleStructure signalType latency).Executes
        initialState inputs outputs finalState) :
    Modules.OptionalShiftRegister.contract signalType latency
      execution.toBoundaryTrace :=
  Modules.OptionalShiftRegister.contract_of_execution signalType latency execution

example :
    (Modules.OptionalShiftRegister.moduleStructure .bit 0).HasNoBlackboxes := by
  native_decide

example :
    (Modules.ShiftRegister.moduleStructure .bit 3 (by omega)).HasNoBlackboxes := by
  native_decide

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def optionalHasRegisterCount (latency : Nat) : Bool :=
  match renderRootModule
      (Modules.OptionalShiftRegister.naming (.vector 4 .bit) latency) with
  | .error _ => false
  | .ok text => occurrences text "inst register_" == latency

#guard optionalHasRegisterCount 0
#guard optionalHasRegisterCount 1
#guard optionalHasRegisterCount 4

private def positiveHasRegisterCount (latency : Nat)
    (positive : 0 < latency) : Bool :=
  match renderRootModule
      (Modules.ShiftRegister.naming (.vector 4 .bit) latency positive) with
  | .error _ => false
  | .ok text => occurrences text "inst register_" == latency

#guard positiveHasRegisterCount 1 (by omega)
#guard positiveHasRegisterCount 4 (by omega)

end SileanTests.ShiftRegisterChecks
