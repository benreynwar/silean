import Silean.Authoring.ModuleDesign
import PicoRV.Decoder.DecoderInstructionMatchGate
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.And

/-! Expanded two-gate representation of one decoder instruction predicate. -/

namespace PicoRV.Decoder.InstructionMatch.MatchGate

open Silean
open Silean.Authoring

module_design Structure (name := "PicoRVDecoderInstructionPredicate") where
  boundary (ports) (naming := Naming.ports)
  instances {
    classAndField (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    qualifiedResult (name := .indexed "and" 1) := Silean.Primitives.andDesign }
  wiring {
    outputs { .result := qualifiedResult.output }
    instance (.classAndField) { .left := input.broad, .right := input.field }
    instance (.qualifiedResult) {
      .left := classAndField.output,
      .right := input.qualifier }
  }

end PicoRV.Decoder.InstructionMatch.MatchGate
