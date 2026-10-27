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
    | .vector n t => s!"!hw.array<{n} x {emitType t}>"
    | .tuple ts => "!hw.struct<" ++ comma (fieldTypes ts 0) ++ ">"
  def fieldTypes : SignalTypes → Nat → List String
  | .nil, _ => []
  | .cons t ts, i => s!"field{i}: {emitType t}" :: fieldTypes ts (i+1)
end

def emitModuleHeader (ifc : CIRCTInterface) : String :=
  let inputs := (List.finRange ifc.ports.nInputs).map fun i =>
    s!"in %{ifc.naming.inputNames i} : {emitType (ifc.ports.inputTypes i)}"
  let clock := match ifc.naming.clkName with
    | none => []
    | some name => [s!"in %{name} : !seq.clock"]
  let outputs := (List.finRange ifc.ports.nOutputs).map fun i =>
    s!"out {ifc.naming.outputNames i} : {emitType (ifc.ports.outputTypes i)}"
  s!"hw.module @{ifc.naming.name}(" ++ comma (inputs ++ clock ++ outputs) ++ ")"

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
    | some fixedName => " {sv.namehint = \"" ++ fixedName ++ "\"}"
    | none => ""
  writeLine s!"%{name} = {text attributes}"
  return s!"%{name}"

def vecBoolToInt (width : Nat) (value : Vector Bool width) : Nat :=
  let indices := List.finRange width
  let rev : Fin width → Fin width := fun i => ⟨width - 1 - i, by omega⟩
  indices.foldl (fun result i => result * 2 + (value[(rev i)]).toNat) 0

mutual
  private def emitConstantValue (t : SignalType) (value : t.Denote) : String :=
    match t with
    | .bit => s!"{Bool.toNat value} : i1"
    | .vector n .bit => s!"{vecBoolToInt n value} : i{n}"
    | .vector n element =>
      let elements : Vector element.Denote n := value
      "[" ++ comma ((List.finRange n).reverse.map (fun i => emitConstantValue element elements[i])) ++ "]"
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
      emitResult maybeName fun attrs => s!"hw.bitcast {s}{attrs} : ({t}) -> {t}"

def refName
    {ctx : Context}
    {t : SignalType} (ref : Ref ctx t)
    : String :=
  match ref with
  | .inputRef i => ctx.ifc.naming.inputNames i
  | .instOutputRef inst port => ctx.insts[inst].outputName port
  | .exprRef i => ctx.exprs[i].name

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
      emitResult name fun attrs => s!"hw.aggregate_constant {literal}{attrs} : {emitType t}"
  | .ref ref => alias s!"%{refName ref}" (emitType t) name
  | .reg next => do
      let nextName := refName next
      let some clk := ctx.ifc.naming.clkName | throw "Register required clock"
      emitResult name fun attrs =>
        s!"seq.firreg %{nextName} clock %{clk}{attrs} : {emitType t}"
  | .add lhs rhs => do
      let lhsName := refName lhs
      let rhsName := refName rhs
      emitResult name fun attrs => s!"comb.add %{lhsName}, %{rhsName}{attrs} : {emitType t}"
  | .sub lhs rhs => do
      let lhsName := refName lhs
      let rhsName := refName rhs
      emitResult name fun attrs => s!"comb.sub %{lhsName}, %{rhsName}{attrs} : {emitType t}"
  | .mul lhs rhs => do
      let lhsName := refName lhs
      let rhsName := refName rhs
      emitResult name fun attrs => s!"comb.mul %{lhsName}, %{rhsName}{attrs} : {emitType t}"
  | .extract (inputWidth := inputWidth) value lowBit outputWidth h => do
      let valueName := refName value
      emitResult name fun attrs => s!"comb.extract %{valueName} from {lowBit}{attrs} : (i{inputWidth}) -> i{outputWidth})"
  | .concat (highWidth := highWidth) (lowWidth := lowWidth) high low => do
      let highName := refName high
      let lowName := refName low
      emitResult name fun attrs => s!"comb.concat %{highName}, %{lowName}{attrs} : i{highWidth}, i{lowWidth}"
  | .replicate (inputWidth := inputWidth) value count positive => do
      let valueName := refName value
      let outputWidth := inputWidth * count
      emitResult name fun attrs => s!"comb.replicate %{valueName}{attrs} : (i{inputWidth}) -> i{outputWidth}"
  | .structExtract (fields := fields) value field => do
      let valueName := refName value
      emitResult name fun attrs => s!"comb.struct_extract %{valueName}{attrs} : {emitType (.tuple fields)}"
  | .structCreate (fields := fields) values => do
      let names := (List.finRange fields.length).map fun i => refName (values i)
      emitResult name fun attrs => s!"comb.struct_create ({comma names}){attrs} : {emitType (.tuple fields)}"

def emitInst (m : CIRCTModule) (i : Fin m.instDecls.size) : PrintM Unit := do
  let inst := m.instDecls[i]
  let ifc := inst.ifc
  -- Build up a list of (name, expr, type) tuples for the input ports
  -- and emit the input port expressions while doing it
  let inputs : List (String × String × String) ← (List.finRange ifc.ports.nInputs).mapM fun j => do
    return (
      ifc.naming.inputNames j,
      s!"%{refName (m.instImpls i j)}",
      emitType (ifc.ports.inputTypes j)
    )
  let outputNames := (List.finRange ifc.ports.nOutputs).map fun port =>
    s!"%{inst.outputName port}"
  let lhs := if outputNames.isEmpty then
    ""
  else
    comma outputNames ++ " = "
  let clocks ← match ifc.naming.clkName with
  | none => pure []
  | some clkName =>
      match m.ifc.naming.clkName with
      | none => throw "Child needs clock but parent doesn't have one"
      | some parentClockName =>
        pure [(clkName, s!"%{parentClockName}", "!seq.clock")]
  let input_text := (inputs ++ clocks).map fun ⟨name, exprname, type⟩ =>
    s!"{name}: {exprname}: {type}"
  let output_text := (List.finRange ifc.ports.nOutputs).map fun j =>
    s!"{ifc.naming.outputNames j} : {emitType (ifc.ports.outputTypes j)}"
  writeLine (
    lhs ++ "hw.instance \"" ++ inst.name ++ "\" @" ++ ifc.naming.name ++
    "(" ++ comma input_text ++ ") -> (" ++ comma output_text ++ ")"
  )

def emitOutput (m : CIRCTModule) (i : Fin m.ifc.ports.nOutputs): PrintM (String × String) := do
  let outputName := refName (m.outputs i)
  return (s!"%{outputName}", emitType (m.ifc.ports.outputTypes i))

def emitBody (m : CIRCTModule) : Except String String := do
  let action : PrintM Unit := do
    for i in List.finRange m.exprDecls.size do
      let _ ← emitExpr m.ctx (m.exprImpls i) (some m.exprDecls[i].name)
    for i in List.finRange m.instDecls.size do
      emitInst m i
    let outputs ← (List.finRange m.ifc.ports.nOutputs).mapM fun i => do
      return ← emitOutput m i
    if outputs.isEmpty then
      writeLine "hw.output"
    else
      writeLine s!"hw.output {comma (outputs.map (·.1))} : {comma (outputs.map (·.2))}"
  let (_, state) ← action.run {}
  return String.intercalate "\n" state.lines ++ "\n"

def emitModule (m : CIRCTModule) : Except String String := do
  m.validateNames
  let header := emitModuleHeader m.ifc
  let body ← emitBody m
  return "  " ++ header ++ "{ \n" ++ body ++ "}\n"

end Silean2.CIRCT
