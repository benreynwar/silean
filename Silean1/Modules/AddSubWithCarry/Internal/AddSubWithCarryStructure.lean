import Silean.Authoring.ModuleDesign
import Silean.Modules.AddSubWithCarry.AddSubWithCarry
import Silean.Modules.BitwiseXor.BitwiseXor
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! Expanded typed structure for the reader-facing add/subtract circuit. -/

module_design AddSubWithCarry (width : Nat) where
  boundary (AddSubWithCarry.ports width)
    (naming := AddSubWithCarry.Naming.ports width)
  instances {
    broadcastSubtract (name := .indexed "combiner" 0) :=
      Silean.Naming.SignalAdapter.combinerDesign
      (AddSubWithCarry.subtractVector width),
    bitwiseXor (name := .indexed "bitwise_xor" 0) :=
      BitwiseXor.design (.vector width .bit),
    add (name := .indexed "add_with_carry" 0) := AddWithCarry.design width }
  named_wires {
    transformedRight := bitwiseXor.result }
  wiring {
    outputs {
      .result := add.result,
      .carryOut := add.carryOut }
    instance (.broadcastSubtract) {
      _ := input.subtract }
    instance (.bitwiseXor) {
      .left := input.right,
      .right := broadcastSubtract.value }
    instance (.add) {
      .left := input.left,
      .right := bitwiseXor.result,
      .carryIn := input.subtract }
  }

end Silean.Modules
