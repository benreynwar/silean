import Silean2.FoundationsH
import Silean2.CIRCT.ModelH

namespace Silean2.CIRCT

open Silean2.Foundations

structure CIRCTBuilder where
  ifc : CIRCTInterface

  exprDecls : List ExprInterface
  instDecls : List InstInterface
  regDecls : List RegInterface
  exprImpls : (index : Fin exprDecls.length) →
    Option (Expr ⟨ifc, exprDecls, instDecls, regDecls⟩ exprDecls[index].type)
  regImpls : (index : Fin regDecls.length) →
    Option (ExprRef ⟨ifc, exprDecls, instDecls, regDecls⟩ regDecls[index].type)
  instImpls : (index : Fin instDecls.length) →
    Option (ExprRefs ⟨ifc, exprDecls, instDecls, regDecls⟩ instDecls[index].ifc.ports.inputTypes)
  outputs : Option (ExprRefs ⟨ifc, exprDecls, instDecls, regDecls⟩ ifc.ports.outputTypes)

abbrev CIRCTBuilder.ctx (b : CIRCTBuilder): Context :=
  ⟨b.ifc, b.exprDecls, b.instDecls, b.regDecls⟩

abbrev CIRCTBuildM := StateT CIRCTBuilder (Except String)

structure ContextUpdate where
  oldCtx : Context
  newExprDecls : List ExprInterface
  newInstDecls : List InstInterface
  newRegDecls : List RegInterface

abbrev ContextUpdate.newCtx (cu : ContextUpdate) : Context := {
  ifc := cu.oldCtx.ifc,
  exprs := cu.oldCtx.exprs ++ cu.newExprDecls
  insts := cu.oldCtx.insts ++ cu.newInstDecls
  regs := cu.oldCtx.regs ++ cu.newRegDecls
}

def appendIndex {α : Type} {before after : List α}
  (i : Fin before.length) : Fin (before ++ after).length :=
  ⟨i.val, by simp; omega⟩


def updateExpr
    {t : SignalType}
    (u : ContextUpdate) (e : Expr u.oldCtx t) : Expr u.newCtx t :=
  match e with
  | .constant value => .constant value
  | .inputRef i => .inputRef (ctx := u.newCtx) i
  | .exprRef i =>
    let newI : Fin u.newCtx.exprs.length := appendIndex i
    have typesEqual : u.newCtx.exprs[newI].type = u.oldCtx.exprs[i].type := by
      simp [newI, appendIndex]
    typesEqual ▸ (.exprRef (ctx := u.newCtx) newI)
  | .regRef i =>
    let newI : Fin u.newCtx.regs.length := appendIndex i
    have typesEqual : u.newCtx.regs[newI].type = u.oldCtx.regs[i].type := by
      simp [newI, appendIndex]
    typesEqual ▸ (.regRef (ctx := u.newCtx) newI)
  | .instOutputRef i o =>
    let newI : Fin u.newCtx.insts.length := appendIndex i
    let newInst := u.newCtx.insts[newI]
    let oldInst := u.oldCtx.insts[i]
    have instanceUnchanged : oldInst = newInst := by
      simp [newI, newInst, oldInst, appendIndex]
    have outputInBounds : o.val < newInst.ifc.ports.nOutputs := by
      simp [newI, newInst, appendIndex]
    let newO : newInst.ifc.ports.OutputKey := ⟨o.val, outputInBounds⟩
    have valsSame : newO.val = o.val := by simp [newO]
    have transport :
      ∀ (a b : InstInterface) (h : a = b)
        (oa : a.ifc.ports.OutputKey) (ob : b.ifc.ports.OutputKey),
        ob.val = oa.val → b.ifc.ports.outputTypes ob = a.ifc.ports.outputTypes oa := by
      intro a b h oa ob hi
      cases h
      have ho : ob = oa := Fin.ext hi
      cases ho
      rfl
    have typesEqual :
      newInst.ifc.ports.outputTypes newO = oldInst.ifc.ports.outputTypes o :=
        transport oldInst newInst instanceUnchanged o newO valsSame
    typesEqual ▸  Expr.instOutputRef (ctx := u.newCtx) newI newO
  | .add a b => .add (updateExpr u a) (updateExpr u b)

def updateInst
    {t : SignalType}
    (u : ContextUpdate)
    (i : Fin u.oldCtx.insts.length)
    (refs : ExprRefs u.oldCtx u.oldCtx.insts[i].ifc.ports.inputTypes)
    : let newI : Fin u.newCtx.insts.length := appendIndex i
      ExprRefs u.newCtx u.newCtx.insts[newI].ifc.ports.inputTypes :=
  fun newPort =>
    let newI : Fin u.newCtx.insts.length := appendIndex i
    let newInst := u.newCtx.insts[newI]
    let oldInst := u.oldCtx.insts[i]
    have instanceUnchanged : oldInst = newInst := by
      simp [newI, newInst, oldInst, appendIndex]
    let oldPort : u.oldCtx.insts[i].ifc.ports.InputKey :=
      ⟨
        newPort.val,
        by
          simp [appendIndex]
      ⟩
    (refs oldPort)

  match e with
  | .constant value => .constant value
  | .inputRef i => .inputRef (ctx := u.newCtx) i
  | .exprRef i =>


end Silean2.CIRCT
