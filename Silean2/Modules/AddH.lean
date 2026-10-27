import Silean2.FoundationsH
import Silean2.CIRCTH

namespace Silean2.Modules.Add

open Silean2.Foundations
open Silean2.CIRCT

abbrev addPorts (width : Nat) : ModulePorts := {
  nInputs := 2
  nOutputs := 1
  inputTypes := fun _ => .vector width .bit
  outputTypes := fun _ => .vector width .bit
}

@[match_pattern]
abbrev left {width : Nat}: (addPorts width).InputKey := ⟨0, by simp⟩
@[match_pattern]
abbrev right {width : Nat}: (addPorts width).InputKey := ⟨1, by simp⟩
@[match_pattern]
abbrev result {width : Nat}: (addPorts width).OutputKey := ⟨0, by simp⟩

def addFunction
    (width : Nat)
    (inputs : (addPorts width).InputValues)
    : (addPorts width).OutputValues :=
  let a := bitVectorToNat (inputs left)
  let b := bitVectorToNat (inputs right)
  let c := (a + b) % (2 ^ width)
  let result : Fin (2 ^ width) := ⟨c, by omega⟩
  fun _ => natToBitVector result

def addSpec (width : Nat) := Spec.ofFunction (addFunction width)

def addBuilder {width : Nat} : CIRCTModuleBuilder (addPorts width) :=
  fun inputs => do
    let sum ← CIRCTBuilder.addExpr "sum"
      (.add (inputs Add.left) (inputs Add.right))
    return fun _ => .exprRef sum

def addImpl (width : Nat) (_ : CIRCTSettings)
    : CIRCTImplementation (addPorts width) := .primitive addBuilder

def addName := "Add"

def addParamsType : ParamsType := .nat

def addRegistration : ModuleRegistration := {
  paramsType := addParamsType
  ports := addPorts
  impl := addImpl
}

def addRef (width : Nat) : ModuleRef (addPorts width) := {
  name := addName,
  paramsType := addParamsType,
  params := width
}




end Silean2.Modules.Add
