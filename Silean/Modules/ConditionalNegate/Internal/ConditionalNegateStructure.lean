import Silean.Authoring.ModuleDesign
import Silean.Modules.BitwiseXor.BitwiseXor
import Silean.Modules.ConditionalNegate.ConditionalNegate
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! Expanded typed structure for the reader-facing conditional-negation
circuit. -/

module_design ConditionalNegate (width : Nat) where
  boundary (ConditionalNegate.ports width)
    (naming := ConditionalNegate.Naming.ports width)
  instances {
    broadcastNegate (name := .indexed "combiner" 0) :=
      Silean.Naming.SignalAdapter.combinerDesign
        (ConditionalNegate.negateVector width),
    bitwiseXor (name := .indexed "bitwise_xor" 0) :=
      BitwiseXor.design (.vector width .bit),
    zero (name := .indexed "constant" 0) :=
      Constant.design (.vector width .bit) (fun _ => false),
    add (name := .indexed "add_with_carry" 0) := AddWithCarry.design width }
  named_wires {
    transformedValue := bitwiseXor.result }
  wiring {
    outputs {
      .result := add.result }
    instance (.broadcastNegate) {
      _ := input.negate }
    instance (.bitwiseXor) {
      .left := input.value,
      .right := broadcastNegate.value }
    instance (.zero) {}
    instance (.add) {
      .left := bitwiseXor.result,
      .right := zero.output,
      .carryIn := input.negate }
  }

end Silean.Modules
