import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Composition.SignalLogic

/-! # Structural equality

Equality compares values of any signal type. Its recursive implementation is
generated under `Internal/`; this file contains the boundary and exact
behavior needed to understand and use its contract.
-/

namespace Silean.Modules.Equality

open Silean
open Silean.Authoring

module_ports ports (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  input left (schema := typeNaming) : signalType,
  input right (schema := typeNaming) : signalType,
  output result : .bit

module_cycle_contract cycleContract (signalType : SignalType)
    for ports signalType where
  state := emptySignalMap
  output_rule apply where
    reads := [left, right]
    writes := { result := signalType.equal left right }
  state_rule where
    reads := []
    next := {}

/-- The equality result is true exactly when the input values are equal. -/
theorem result_eq_true_iff_of_allowed (signalType : SignalType)
    {step : (cycleContract signalType).Step}
    (allowed : (cycleContract signalType).Allows step) :
    step.outputs .result = true ↔ step.inputs .left = step.inputs .right := by
  rw [cycleContract.result signalType allowed]
  exact signalType.equal_eq_true_iff _ _

end Silean.Modules.Equality
