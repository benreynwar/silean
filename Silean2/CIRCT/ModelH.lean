import Std.Data.HashMap
import Silean2.Foundations.SignalTypeH
import Silean2.Foundations.PortsH

namespace Silean2.CIRCT

open Silean2.Foundations

structure CIRCTNaming (ports : ModulePorts) where
  name : String
  clkName : Option String
  inputNames : ports.InputKey → String := fun i => s!"input{i.val}"
  outputNames : ports.OutputKey → String := fun i => s!"output{i.val}"

structure CIRCTInterface where
  ports : ModulePorts
  naming : CIRCTNaming ports

structure ExprInterface where
  name : String
  type : SignalType

structure InstInterface where
  name : String
  ifc : CIRCTInterface

def InstInterface.outputName
    (inst : InstInterface)
    (port : inst.ifc.ports.OutputKey)
    : String :=
  s!"{inst.name}_{inst.ifc.naming.outputNames port}"

structure Context where
  ifc : CIRCTInterface
  exprs : Array ExprInterface
  insts : Array InstInterface

abbrev CIRCTInt (width : Nat) := SignalType.vector width SignalType.bit

inductive Ref (ctx : Context) : SignalType → Type
  | exprRef (exprIndex : Fin ctx.exprs.size) : Ref ctx (ctx.exprs[exprIndex].type)
  | inputRef (inputIndex : ctx.ifc.ports.InputKey) : Ref ctx (ctx.ifc.ports.inputTypes inputIndex)
  | instOutputRef (instIndex : Fin ctx.insts.size)
    (nodeOutputIndex : Fin ctx.insts[instIndex].ifc.ports.nOutputs)
    : Ref ctx (ctx.insts[instIndex].ifc.ports.outputTypes nodeOutputIndex)

inductive Expr (ctx : Context) : SignalType → Type
  | constant {t : SignalType} (value : t.Denote) : Expr ctx t
  | ref {t : SignalType} (ref : Ref ctx t) : Expr ctx t
  | reg {t : SignalType} (next : Ref ctx t) : Expr ctx t
  | add {width : Nat} (lhs : Ref ctx (CIRCTInt width)) (rhs : Ref ctx (CIRCTInt width))
    : Expr ctx (CIRCTInt width)
  | sub {width : Nat} (lhs : Ref ctx (CIRCTInt width)) (rhs : Ref ctx (CIRCTInt width))
    : Expr ctx (CIRCTInt width)
  | mul {width : Nat} (lhs : Ref ctx (CIRCTInt width)) (rhs : Ref ctx (CIRCTInt width))
    : Expr ctx (CIRCTInt width)
  | extract {inputWidth : Nat}
      (value : Ref ctx (CIRCTInt inputWidth))
      (lowBit outputWidth : Nat)
      (inBounds : lowBit + outputWidth ≤ inputWidth)
    : Expr ctx (CIRCTInt outputWidth)
  | concat {highWidth lowWidth : Nat}
      (high : Ref ctx (CIRCTInt highWidth)) (low : Ref ctx (CIRCTInt lowWidth))
    : Expr ctx (CIRCTInt (highWidth + lowWidth))
  | replicate {inputWidth: Nat}
      (value : Ref ctx (CIRCTInt inputWidth))
      (count : Nat) (positive : 0 < count)
    : Expr ctx (CIRCTInt (inputWidth * count))
  | structExtract {fields : SignalTypes}
      (value : Ref ctx (.tuple fields))
      (field : Fin fields.length)
    : Expr ctx (fields.get field)
  | structCreate {fields : SignalTypes}
      (values : (i : Fin fields.length) → Ref ctx (fields.get i))
    : Expr ctx (.tuple fields)



abbrev Refs (ctx : Context) {nPorts : Nat} (types : PortTypes nPorts) :=
  (i : Fin nPorts) → Ref ctx (types i)

abbrev ExprImpls (ctx : Context) :=
  (index : Fin ctx.exprs.size) → Expr ctx ctx.exprs[index].type
abbrev InstImpls (ctx : Context) :=
  (index : Fin ctx.insts.size) → Refs ctx ctx.insts[index].ifc.ports.inputTypes
abbrev OutputImpls (ctx : Context) :=
  Refs ctx ctx.ifc.ports.outputTypes

structure CIRCTModule where
  ifc : CIRCTInterface
  exprDecls : Array ExprInterface
  instDecls : Array InstInterface
  exprImpls : ExprImpls ⟨ifc, exprDecls, instDecls⟩
  instImpls : InstImpls ⟨ifc, exprDecls, instDecls⟩
  outputs : OutputImpls ⟨ifc, exprDecls, instDecls⟩

abbrev CIRCTModule.ctx (m : CIRCTModule) : Context := ⟨m.ifc, m.exprDecls, m.instDecls⟩

def validName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | head :: tail =>
      (head.isAlpha || head == '_') &&
      tail.all (fun c => head.isAlphanum || c == '_')

def checkName (origin name : String) : Except String Unit :=
  if !(validName name) then
    throw s!"Invalid {origin} name {name}. Expected [A-Za-z_][A-Za-z0-9_]*"
  else
    pure ()

def checkUniqueNames (scope : String) (names : List (String × String)) : Except String Unit := do
  let mut seen : Std.HashMap String String := {}
  for (name, origin) in names do
    checkName origin name
    match seen[name]? with
    | none => seen := seen.insert name origin
    | some previous => throw s!"Duplicate name {name} in {scope}: {previous} and {origin}"

def CIRCTInterface.validateNames (ifc : CIRCTInterface) : Except String Unit := do
  checkName "module" ifc.naming.name
  let inputs := (List.finRange ifc.ports.nInputs).map fun p =>
    (ifc.naming.inputNames p, s!"input {p}")
  let outputs := (List.finRange ifc.ports.nOutputs).map fun p =>
    (ifc.naming.outputNames p, s!"output {p}")
  let clock := match ifc.naming.clkName with
  | none => []
  | some clockName  => [(clockName, "clock")]
  checkUniqueNames s!"inputs of module {ifc.naming.name}" (inputs ++ clock)
  checkUniqueNames s!"outputs of module {ifc.naming.name}" outputs


def CIRCTModule.validateNames (m : CIRCTModule) : Except String Unit := do
  m.ifc.validateNames
  for inst in m.instDecls do
    inst.ifc.validateNames

  -- Make sure every child instance has a unique name.
  checkUniqueNames s!"instances in module {m.ifc.naming.name}"
    ((List.finRange m.instDecls.size).map fun i =>
      (m.instDecls[i].name, s!"instance {i.val}"))

  -- Check all the SSA names
  let inputs := (List.finRange m.ifc.ports.nInputs).map fun p =>
    (m.ifc.naming.inputNames p, s!"input {p.val}")
  let clock := match m.ifc.naming.clkName with
  | none => []
  | some clockName  => [(clockName, "clock")]
  let exprs := (List.finRange m.exprDecls.size).map fun i =>
    (m.exprDecls[i].name, s!"expr {i.val}")
  let instOutputs := (List.finRange m.instDecls.size).flatMap fun i =>
    (List.finRange m.instDecls[i].ifc.ports.nOutputs).map fun p =>
      (m.instDecls[i].outputName p, s!"instance {i.val} output {p.val}")
  checkUniqueNames s!"SSA values of module {m.ifc.naming.name}"
    (inputs ++ clock ++ exprs ++ instOutputs)


end Silean2.CIRCT
