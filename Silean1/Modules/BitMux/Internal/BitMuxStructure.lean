import Silean.Authoring.ModuleDesign
import Silean.Modules.BitMux.BitMux
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.AndPrimitive
import Silean.Primitives.NotPrimitive
import Silean.Primitives.OrPrimitive

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! Expanded typed structure for the reader-facing bit-mux description. -/

module_design BitMux where
  boundary (BitMux.ports) (naming := BitMux.Naming.ports)
  instances {
    invertSelect (name := .indexed "not" 0) := Primitives.notDesign,
    chooseFalse (name := .indexed "and" 0) := Primitives.andDesign,
    chooseTrue (name := .indexed "and" 1) := Primitives.andDesign,
    combine (name := .indexed "or" 0) := Primitives.orDesign }
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
