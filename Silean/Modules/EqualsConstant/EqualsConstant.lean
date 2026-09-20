import Silean.Authoring.CircuitLogic
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Modules.Constant.Constant

/-! # Comparison with a constant

The authored circuit places a constant source beside an equality comparison.
Its contract states the resulting comparison independently of that structure.
-/

namespace Silean.Modules.EqualsConstant

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring

module_ports ports (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  input value (schema := typeNaming) : signalType,
  output result : .bit

open ports

noncomputable def construction (signalType : SignalType)
    (fixedValue : signalType.Denote) : ModuleBuilder (ports signalType) Unit := do
  let value ← input signalType .value
  output signalType .result (← value === (← constant signalType fixedValue))

noncomputable def description (signalType : SignalType)
    (fixedValue : signalType.Denote) : Description :=
  ModuleBuilder.build (Naming.ports signalType)
    (construction signalType fixedValue)

module_cycle_contract cycleContract (signalType : SignalType)
    (fixedValue : signalType.Denote) for ports signalType where
  state := emptySignalMap
  output_rule apply where
    reads := [value]
    writes := { result := signalType.equal value fixedValue }
  state_rule where
    reads := []
    next := {}

/-- The comparison is true exactly when the input equals the fixed value. -/
theorem result_eq_true_iff_of_allowed (signalType : SignalType)
    (fixedValue : signalType.Denote)
    {step : (cycleContract signalType fixedValue).Step}
    (allowed : (cycleContract signalType fixedValue).Allows step) :
    step.outputs .result = true ↔ step.inputs .value = fixedValue := by
  rw [cycleContract.result signalType fixedValue allowed]
  exact signalType.equal_eq_true_iff _ _

end Silean.Modules.EqualsConstant
