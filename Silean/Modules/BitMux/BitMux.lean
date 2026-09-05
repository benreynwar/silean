import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.AndPrimitive
import Silean.Primitives.NotPrimitive
import Silean.Primitives.OrPrimitive

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A one-bit combinational mux built directly from Boolean gates. -/

module_design BitMux where
  ports {
    input select : .bit,
    input whenFalse : .bit,
    input whenTrue : .bit,
    output result : .bit }
  instances {
    -- Produces the complement of `select`.
    invertSelect := Primitives.notDesign,
    -- Passes `whenFalse` only when `select` is low.
    chooseFalse := Primitives.andDesign,
    -- Passes `whenTrue` only when `select` is high.
    chooseTrue := Primitives.andDesign,
    -- Combines the mutually exclusive selected values.
    combine := Primitives.orDesign }
  wiring {
    outputs {
      .result := combine.output }
    instance (.invertSelect) {
      .input := input.select }
    instance (.chooseFalse) {
      .left := input.whenFalse,
      .right := invertSelect.output }
    instance (.chooseTrue) {
      .left := input.whenTrue,
      .right := input.select }
    instance (.combine) {
      .left := chooseFalse.output,
      .right := chooseTrue.output }
  }

end Silean.Modules

namespace Silean.Modules.BitMux

open Silean
open Silean.Authoring

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule select where
    reads := [select, whenFalse, whenTrue]
    writes := { result := bif select then whenTrue else whenFalse }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.BitMux
