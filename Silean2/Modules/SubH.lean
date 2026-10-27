import Silean2.FoundationsH
import Silean2.CIRCTH

namespace Silean2.Modules.Sub

open Silean2.Foundations
open Silean2.CIRCT

abbrev subPorts (width : Nat) : ModulePorts := {
  nInputs := 2
  nOutputs := 1
  inputTypes := fun _ => .vector width .bit
  outputTypes := fun _ => .vector width .bit
}

@[match_pattern]
abbrev left {width : Nat}: (subPorts width).InputKey := ⟨0, by simp⟩
@[match_pattern]
abbrev right {width : Nat}: (subPorts width).InputKey := ⟨1, by simp⟩
@[match_pattern]
abbrev result {width : Nat}: (subPorts width).OutputKey := ⟨0, by simp⟩

def subFunction
    (width : Nat)
    (inputs : (subPorts width).InputValues)
    : (subPorts width).OutputValues :=
  let a := bitVectorToNat (inputs left)
  let b := bitVectorToNat (inputs right)
  let c := (a - b) % (2 ^ width)
  let result : Fin (2 ^ width) := ⟨c, by omega⟩
  fun _ => natToBitVector result

def subSpec (width : Nat) := Spec.ofFunction (subFunction width)

def subBuilder {width : Nat} : CIRCTModuleBuilder (subPorts width) :=
  fun inputs => do
    let sum ← CIRCTBuilder.addExpr "result"
      (.sub (inputs Sub.left) (inputs Sub.right))
    return fun _ => .exprRef sum

def subImpl (width : Nat) (_ : CIRCTSettings)
    : CIRCTImplementation (subPorts width) := .primitive subBuilder

def subName := "Sub"

def subParamsType : RawParamsType := .nat

def subRegistration : ModuleRegistration := {
  rawParamsType := subParamsType
  ParamsType := Nat
  decodeParams := fun x => pure x
  ports := subPorts
  impl := subImpl
}

def subRef (width : Nat) : ModuleRef (subPorts width) := {
  name := subName,
  paramsType := subParamsType,
  params := width
}

end Silean2.Modules.Sub
