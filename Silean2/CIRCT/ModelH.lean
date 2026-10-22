import Silean2.Foundations.SignalTypeH
import Silean2.Foundations.PortsH

namespace Silean2.CIRCT

open Silean2.Foundations

structure CIRCTInterface where
  name : String
  ports : ModulePorts
  clkName : Option String
  inputNames : ports.InputKey → String := fun i => s!"input{i.val}"
  outputNames : ports.OutputKey → String := fun i => s!"output{i.val}"

structure ExprInterface where
  name : String
  type : SignalType

structure InstInterface where
  name : String
  ifc : CIRCTInterface

structure RegInterface where
  name : String
  type : SignalType

structure Context where
  ifc : CIRCTInterface
  exprs : List ExprInterface
  insts : List InstInterface
  regs : List RegInterface

abbrev CIRCTInt (width : Nat) := SignalType.vector width SignalType.bit

inductive ExprRef (ctx : Context) : SignalType → Type
  | ref (exprIndex : Fin ctx.exprs.length) : ExprRef ctx (ctx.exprs[exprIndex].type)

def ExprRef.index : (r : ExprRef ctx signalType) → Fin ctx.exprs.length
  | ref exprIndex => exprIndex

inductive Expr (ctx : Context) : SignalType → Type
  | constant {t : SignalType} (value : t.Denote) : Expr ctx t
  | inputRef (inputIndex : ctx.ifc.ports.InputKey) : Expr ctx (ctx.ifc.ports.inputTypes inputIndex)
  | exprRef (exprIndex : Fin ctx.exprs.length) : Expr ctx (ctx.exprs[exprIndex].type)
  | regRef (regIndex : Fin ctx.regs.length) : Expr ctx (ctx.regs[regIndex].type)
  | instOutputRef
    (instIndex : Fin ctx.insts.length)
    (nodeOutputIndex : Fin ctx.insts[instIndex].ifc.ports.nOutputs)
    : Expr ctx (ctx.insts[instIndex].ifc.ports.outputTypes nodeOutputIndex)
  | add {width : Nat} (lhs : Expr ctx (CIRCTInt width)) (rhs : Expr ctx (CIRCTInt width))
    : Expr ctx (CIRCTInt width)

abbrev ExprRefs (ctx : Context) {nPorts : Nat} (types : PortTypes nPorts) :=
  (i : Fin nPorts) → ExprRef ctx (types i)

structure CIRCTModule where
  ifc : CIRCTInterface

  exprDecls : List ExprInterface
  instDecls : List InstInterface
  regDecls : List RegInterface
  exprImpls : (index : Fin exprDecls.length) →
    Expr ⟨ifc, exprDecls, instDecls, regDecls⟩ exprDecls[index].type
  regImpls : (index : Fin regDecls.length) →
    ExprRef ⟨ifc, exprDecls, instDecls, regDecls⟩ regDecls[index].type
  instImpls : (index : Fin instDecls.length) →
    ExprRefs ⟨ifc, exprDecls, instDecls, regDecls⟩ instDecls[index].ifc.ports.inputTypes
  outputs : (index : ifc.ports.OutputKey) →
    ExprRef ⟨ifc, exprDecls, instDecls, regDecls⟩ (ifc.ports.outputTypes index)

abbrev CIRCTModule.ctx (m : CIRCTModule) : Context := ⟨m.ifc, m.exprDecls, m.instDecls, m.regDecls⟩

end Silean2.CIRCT
