import Silean2.FoundationsH
import Silean2.CIRCTH
import Silean2.Modules.AddH

namespace Silean2.Modules.AddWrapper

open Silean2.Foundations
open Silean2.CIRCT

abbrev addWrapperPorts (width : Nat) : ModulePorts := {
  nInputs := 2
  nOutputs := 1
  inputTypes := fun _ => .vector width .bit
  outputTypes := fun _ => .vector width .bit
}

abbrev left {width : Nat}: (addWrapperPorts width).InputKey := ⟨0, by simp⟩
abbrev right {width : Nat}: (addWrapperPorts width).InputKey := ⟨1, by simp⟩
abbrev result {width : Nat}: (addWrapperPorts width).OutputKey := ⟨0, by simp⟩

def addWrapperFunction
    (width : Nat)
    (inputs : (addWrapperPorts width).InputValues)
    : (addWrapperPorts width).OutputValues :=
  let a := bitVectorToNat (inputs left)
  let b := bitVectorToNat (inputs right)
  let c := (a + b) % (2 ^ width)
  let result : Fin (2 ^ width) := ⟨c, by omega⟩
  fun _ => natToBitVector result

def addWrapperSpec (width : Nat) := Spec.ofFunction (addWrapperFunction width)

open Silean2.Modules

def addWrapperFromAdd (width : Nat) : ModuleBody := {
  ports := addWrapperPorts width
  nChildren := 1
  childPorts := fun _ => Add.addPorts width
  childInputDrivers := fun _ p => match p with
    | Add.left => Source.input left
    | Add.right => Source.input right
  outputDrivers := fun _ => Source.childOutput 0 Add.result
}

def addWrapperParamsType : ParamsType:= .nat

namespace AddWrapperFromAdd

abbrev childSpecs (width : Nat) : ChildSpecs (addWrapperFromAdd width) := fun _ => (Add.addSpec width)

def childImpls (width : Nat) (_ : Fin 1) := Add.addImpl width


def addWrapperFromAddBuilder {width : Nat} : CIRCTModuleBuilder (addWrapperPorts width) :=
  fun inputs => do
    let sum ← CIRCTBuilder.addExpr "sum"
      (.add (inputs Add.left) (inputs Add.right))
    return fun _ => .exprRef sum

def addWrapperFromAddImpl (width : Nat) (_ : CIRCTSettings)
    : CIRCTImplementation (addWrapperPorts width) :=
  .composite (addWrapperFromAdd width) {
    name := s!"AddWrapper_{width}"
    clkName := none
  }
  (fun _child _settings => Add.addRef width)

def addWrapperFromAddName := "AddWrapperFromAdd"
def addWrapperFromAddRegistration : ModuleRegistration := {
  paramsType := .nat
  ports := addWrapperPorts
  impl := addWrapperFromAddImpl
}
def addWrapperFromAddRef (width : Nat): ModuleRef (addWrapperPorts width) := {
  name := addWrapperFromAddName,
  paramsType := addWrapperParamsType,
  params := width,
}

end AddWrapperFromAdd


end Silean2.Modules.AddWrapper
