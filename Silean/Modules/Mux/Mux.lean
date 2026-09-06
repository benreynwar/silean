import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Modules.Mask.Mask
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.NotPrimitive

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A generic combinational mux built from masking and bitwise OR. -/

module_design Mux (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  ports {
    input select : .bit,
    input whenFalse (schema := typeNaming) : signalType,
    input whenTrue (schema := typeNaming) : signalType,
    output result (schema := typeNaming) : signalType }
  instances {
    -- Produces the complement of the select bit.
    invertSelect := Primitives.notDesign,
    -- Passes the false branch only when select is low.
    chooseFalse := Mask.design signalType,
    -- Passes the true branch only when select is high.
    chooseTrue := Mask.design signalType,
    -- Combines the two mutually exclusive masked values.
    combine := BitwiseOr.design signalType }
  wiring {
    outputs {
      .result := combine.result }
    instance (.invertSelect) {
      .input := input.select }
    instance (.chooseFalse) {
      .value := input.whenFalse,
      .mask := invertSelect.output }
    instance (.chooseTrue) {
      .value := input.whenTrue,
      .mask := input.select }
    instance (.combine) {
      .left := chooseFalse.result,
      .right := chooseTrue.result }
  }

end Silean.Modules

namespace Silean.Modules.Mux

open Silean
open Silean.Authoring

/-! ## Exact cycle behavior -/

module_cycle_contract cycleContract (signalType : SignalType)
    for ports signalType where
  state := emptySignalMap
  output_rule select where
    reads := [select, whenFalse, whenTrue]
    writes := {
      result := bif select then whenTrue else whenFalse }
  state_rule where
    reads := []
    next := {}

/-- Contract-facing selection law for the generic mux. -/
theorem result_of_evaluatesTo (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signalType).outputs.Values) (nextState : emptySignalMap.Values)
    (evaluates : (cycleContract signalType).EvaluatesTo inputs state outputs nextState) :
    outputs .result = bif inputs .select then inputs .whenTrue else inputs .whenFalse := by
  exact (selectRule_holds_iff signalType inputs state outputs).mp
    (evaluates.1 Rule.select)

end Silean.Modules.Mux
