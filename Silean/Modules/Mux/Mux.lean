import Silean.Authoring.CircuitDescription
import Silean.Modules.Mux.MuxContract
import Silean.Modules.Mask.Mask
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Naming.PrimitiveNaming

/-! Builder-authored Mux. Correspondence with production is proved separately
in `MuxCertified.lean`. -/

namespace Silean.Modules.Mux.Description

open Silean Naming Authoring.CircuitDescription

private def invert (name : SourceName) (value : Net .bit) : Builder (Net .bit) := do
  let child ← place name Primitives.notDesign (fun _ => value)
  pure (child .output)

private noncomputable def mask (name : SourceName) (value : Net signalType)
    (enabled : Net .bit) : Builder (Net signalType) := do
  let child ← place name (Mask.design signalType) fun
    | .value => value
    | .mask => enabled
  pure (child .result)

private noncomputable def bitwiseOr (name : SourceName) (left right : Net signalType) :
    Builder (Net signalType) := do
  let child ← place name (BitwiseOr.design signalType) fun
    | .left => left
    | .right => right
  pure (child .result)

/-- Ordinary do notation; existing children retain their full production identity. -/
noncomputable def construction (signalType : SignalType) : Builder Unit := do
  let select ← input "select" .bit
  let whenFalse ← input "whenFalse" signalType
  let whenTrue ← input "whenTrue" signalType
  let inverted ← invert "invertSelect" select
  let falseValue ← mask "chooseFalse" whenFalse inverted
  let trueValue ← mask "chooseTrue" whenTrue select
  let result ← bitwiseOr "combine" falseValue trueValue
  output "result" result

noncomputable def description (signalType : SignalType) := build (construction signalType)


end Silean.Modules.Mux.Description
