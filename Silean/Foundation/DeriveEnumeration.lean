import Silean.Foundation.Enumeration
import Lean.Elab.Deriving.Basic

namespace Silean

open Lean Elab Command Parser Term

private def nestedTail : Nat → CommandElabM (TSyntax `term)
  | 0 => `(.head)
  | depth + 1 => do `(.tail $(← nestedTail depth))

private def deriveEnumeration (declNames : Array Name) : CommandElabM Bool := do
  for declName in declNames do
    let .inductInfo info ← getConstInfo declName
      | return false
    unless info.levelParams.isEmpty && info.numParams == 0 &&
        info.numIndices == 0 && !info.ctors.isEmpty do
      return false
    let mut constructors : Array (TSyntax `term) := #[]
    let mut alternatives : Array (TSyntax ``matchAlt) := #[]
    for ctorName in info.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      unless ctorInfo.numFields == 0 do
        return false
      let constructor := mkCIdent ctorName
      constructors := constructors.push constructor
      let pattern ← `($constructor)
      let rhs ← nestedTail alternatives.size
      alternatives := alternatives.push (← `(matchAltExpr| | $pattern => $rhs))
    let values ← `([$[$constructors],*])
    let locate ← `(fun value => match value with $alternatives:matchAlt*)
    elabCommand <| ← withFreshMacroScope `(
      instance : Enumeration @$(mkCIdent declName) where
        values := $values
        nodup := by simp
        locate := $locate
    )
  return true

initialize
  registerDerivingHandler ``Enumeration deriveEnumeration

end Silean
