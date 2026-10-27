import Silean2.FoundationsH
import Silean2.CIRCTH

namespace Silean2.Modules.Mul

open Silean2.Foundations
open Silean2.CIRCT

abbrev mulPorts (width : Nat) : ModulePorts := {
  nInputs := 2
  nOutputs := 1
  inputTypes := fun _ => .vector width .bit
  outputTypes := fun _ => .vector width .bit
}

@[match_pattern]
abbrev left {width : Nat}: (mulPorts width).InputKey := ⟨0, by simp⟩
@[match_pattern]
abbrev right {width : Nat}: (mulPorts width).InputKey := ⟨1, by simp⟩
@[match_pattern]
abbrev result {width : Nat}: (mulPorts width).OutputKey := ⟨0, by simp⟩

def mulFunction
    (width : Nat)
    (inputs : (mulPorts width).InputValues)
    : (mulPorts width).OutputValues :=
  let a := bitVectorToNat (inputs left)
  let b := bitVectorToNat (inputs right)
  let c := (a * b) % (2 ^ width)
  let result : Fin (2 ^ width) := ⟨c, by omega⟩
  fun _ => natToBitVector result

def mulSpec (width : Nat) := Spec.ofFunction (mulFunction width)

def mulBuilder {width : Nat} : CIRCTModuleBuilder (mulPorts width) :=
  fun inputs => do
    let sum ← CIRCTBuilder.addExpr "result"
      (.mul (inputs Mul.left) (inputs Mul.right))
    return fun _ => .exprRef sum

def mulImpl (width : Nat) (_ : CIRCTSettings)
    : CIRCTImplementation (mulPorts width) := .primitive mulBuilder

def mulName := "Mul"

def mulParamsType : RawParamsType := .nat

def mulRegistration : ModuleRegistration := {
  rawParamsType := mulParamsType
  ParamsType := Nat
  decodeParams := fun x => pure x
  ports := mulPorts
  impl := mulImpl
}

def mulRef (width : Nat) : ModuleRef (mulPorts width) := {
  name := mulName,
  paramsType := mulParamsType,
  params := width
}

end Silean2.Modules.Mul
