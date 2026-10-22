import Lean
import Std
import Silean2.CIRCT.ModelH
import Silean2.Foundations.SignalTypeH

namespace Silean2.CIRCT

open Lean
open Silean2.Foundations

private def comma (xs : List String) : String := String.intercalate ", " xs


mutual
  def emitType : SignalType → String
    | .bit => "i1"
    | .vector n .bit => s!"i{n}"
    | .vector n t => s!"!hw.array<{n} x {emitType t}"
    | .tuple ts => "!hw.struct<" ++ comma (fieldTypes ts 0) ++ ">"
  def fieldTypes : SignalTypes → Nat → List String
  | .nil, _ => []
  | .cons t ts, i => s!"field{i}: {emitType t}" :: fieldTypes ts (i+1)
end

def emitModuleHeader (ifc : CIRCTInterface) : String :=
  let inputs := (List.finRange ifc.ports.nInputs).map fun i =>
    s!"in %{ifc.inputNames i} : {emitType (ifc.ports.inputTypes i)}"
  let clock := match ifc.clkName with
    | none => []
    | some name => [s!"in %{name} : !seq.clock"]
  let outputs := (List.finRange ifc.ports.nOutputs).map fun i =>
    s!"out %{ifc.outputNames i} : {emitType (ifc.ports.outputTypes i)}"
  s!"hw.module @{ifc.name}(" ++ comma (inputs ++ clock ++ outputs) ++ ")"

private structure PrintState where
  lines : List String := []
  -- `next` is used to generate names for intermediates with.
  -- It gets incremented after each use.
  next : Nat := 0

private abbrev PrintM := StateT PrintState (Except String)

def writeLine (s : String) : PrintM Unit :=
  modify fun st => { st with lines := st.lines ++ ["    " ++ s] }

def freshName : PrintM String := do
  let index := (← get).next
  let name := s!"val{index}"
  modify fun st => { st with next := st.next + 1 }
  return name

def emitResult (maybeName : Option String)
    (text : String → String) : PrintM String := do
  let name ← match maybeName with
    | some fixedName => pure fixedName
    | none => freshName
  let attributes := match maybeName with
    | some fixedName => " {sv.namehint := " ++ fixedName ++ "}"
    | none => ""
  writeLine s!"%{name} = {text attributes}"
  return s!"%{name}"

def vecBoolToInt (width : Nat) (value : Fin width → Bool) : Nat :=
  let indices := List.finRange width
  indices.foldl (fun result i => result * 2 + (value i).toNat) 0

mutual
  private def emitConstantValue (t : SignalType) (value : t.Denote) : String :=
    match t with
    | .bit => s!"{Bool.toNat value} : i1"
    | .vector n .bit => s!"{vecBoolToInt n value} : i{n}"
    | .vector n element =>
      "[" ++ comma ((List.finRange n).reverse.map (fun i => emitConstantValue element (value i))) ++ "]"
    | .tuple elements =>
      "[" ++ comma (emitConstantFields elements value) ++ "]"

  private def emitConstantFields (ts : SignalTypes) (value : ts.Denote) : List String :=
    match ts with
    | .nil => []
    | .cons t tail => emitConstantValue t value.1 :: emitConstantFields tail value.2

end

def alias (s : String) (t : String) (maybeName : Option String) : PrintM String := do
  match maybeName with
  | none => return s
  | some name =>
    if s!"%{name}" == s then
      return s
    else
      emitResult maybeName fun attrs => s!"hw.bitcast {s}{attrs} : ({t}) → {t}"

def emitExpr
    (ctx : Context)
    {t : SignalType} (e : Expr ctx t)
    (name : Option String)
    : PrintM String :=
  match e with
  | .constant value =>
    let literal := emitConstantValue t value
    match t with
    | .bit | .vector _ .bit =>
      emitResult name fun attrs => s!"hw.constant {literal}{attrs}"
    | _ =>
      emitResult name fun attrs => s!"hw.aggregate_constant {literal}{attrs}"
  | .inputRef i => alias s!"%{ctx.ifc.inputNames i}" (emitType t) name
  | .exprRef i => alias s!"%{ctx.exprs[i].name}" (emitType t) name
  | .regRef i => alias s!"%{ctx.regs[i].name}" (emitType t) name
  | .instOutputRef i j => alias s!"%{ctx.insts[i].ifc.outputNames j}" (emitType t) name
  | .add lhs rhs => do
      let lhsName ← emitExpr ctx lhs none
      let rhsName ← emitExpr ctx rhs none
      emitResult name fun attrs => s!"comb.add {lhsName}, {rhsName}{attrs} : {emitType t}"

def emitInst (m : CIRCTModule) (i : Fin m.instDecls.length) : PrintM Unit := do
  let inst := m.instDecls[i]
  let ifc := inst.ifc
  -- Build up a list of (name, expr, type) tuples for the input ports
  -- and emit the input port expressions while doing it
  let inputs : List (String × String × String) ← (List.finRange ifc.ports.nInputs).mapM fun j => do
    return (
      ifc.inputNames j,
      m.exprDecls[(m.instImpls i j).index].name,
      emitType (ifc.ports.inputTypes j)
    )
  let outputNames := (List.finRange ifc.ports.nOutputs).map fun j => s!"%{ifc.outputNames j}"
  let lhs := if outputNames.isEmpty then
    ""
  else
    comma outputNames ++ " = "
  let clocks ← match ifc.clkName with
  | none => pure []
  | some clkName =>
      match m.ifc.clkName with
      | none => throw "Child needs clock but parent doesn't have one"
      | some parentClockName =>
        pure [(clkName, s!"%{parentClockName}", "!seq.clock")]
  let input_text := (inputs ++ clocks).map fun ⟨name, exprname, type⟩ =>
    s!"{name}: {exprname}: {type}"
  let output_text := (List.finRange ifc.ports.nOutputs).map fun j =>
    s!"%{ifc.outputNames j} : {emitType (ifc.ports.outputTypes j)}"
  writeLine (
    lhs ++ "hw.instance" ++ inst.name ++ " @" ++ ifc.name ++
    "(" ++ comma input_text ++ ") -> (" ++ comma output_text ++ ")"
  )

def emitReg (m : CIRCTModule) (i : Fin m.regDecls.length) : PrintM Unit := do
  let regDecl := m.regDecls[i]
  let exprIndex := (m.regImpls i).index
  let nextName := m.exprDecls[exprIndex].name
  let some clk := m.ifc.clkName | throw "Register required clock"
  let _ ← emitResult (some regDecl.name) fun attrs =>
    s!"seq.firreg {nextName} clock %{clk}{attrs} : {emitType regDecl.type}"

def emitOutput (m : CIRCTModule) (i : Fin m.ifc.ports.nOutputs): PrintM (String × String) := do
  let outputName := m.exprDecls[(m.outputs i).index].name
  return (outputName, emitType (m.ifc.ports.outputTypes i))

def emitBody (m : CIRCTModule) : Except String String := do
  let action : PrintM Unit := do
    for i in List.finRange m.exprDecls.length do
      let _ ← emitExpr m.ctx (m.exprImpls i) (some m.exprDecls[i].name)
    for i in List.finRange m.instDecls.length do
      emitInst m i
    for i in List.finRange m.regDecls.length do
      emitReg m i
    let outputs ← (List.finRange m.ifc.ports.nOutputs).mapM fun i => do
      return ← emitOutput m i
    if outputs.isEmpty then
      writeLine "hw.output"
    else
      writeLine "s!hw.output {comma (outputs.map (·.1))} : {comma (outputs.map (·.2))}"
  let (_, state) ← action.run {}
  return String.intercalate "\n" state.lines ++ "\n"

def emitModule (m : CIRCTModule) : Except String String := do
  let header := emitModuleHeader m.ifc
  let body ← emitBody m
  return "  " ++ header ++ body

end Silean2.CIRCT
