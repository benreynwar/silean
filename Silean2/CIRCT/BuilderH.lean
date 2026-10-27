import Std.Data.HashMap
import Silean2.FoundationsH
import Silean2.CIRCT.ModelH
import Silean2.CIRCT.RegistryH

namespace Silean2.CIRCT

open Silean2.Foundations

def CIRCTBuilder.declareExpr
    (t : SignalType)
    (name : String)
    : CIRCTBuildM Nat := do
  let b ← get
  let name := if name.isEmpty then s!"expr{b.exprs.size}" else name
  let newExprs := b.exprs.push {name := name, type := t, impl := none}
  set {b with exprs := newExprs }
  return b.exprs.size

def CIRCTBuilder.defineExpr
    (i : Nat)
    {t : SignalType}
    (e : BuilderExpr t)
    : CIRCTBuildM Unit := do
  let b ← get
  let checkedI ← checkedFin b.exprs.size i
  let slot := b.exprs[checkedI]
  let expectedType := b.exprs[checkedI].type
  let checkedE ← checkedCast expectedType e
  set { b with
    exprs := b.exprs.set checkedI {slot with impl := some checkedE}
  }

def CIRCTBuilder.addExpr
    {t : SignalType}
    (name : String)
    (e : BuilderExpr t)
    : CIRCTBuildM Nat := do
  let b ← get
  let name := if name.isEmpty then s!"expr{b.exprs.size}" else name
  let newExprs := b.exprs.push {name := name, type := t, impl := some e}
  set {b with exprs := newExprs }
  return b.exprs.size

def CIRCTBuilder.declareInst
    (name : String)
    (ifc : CIRCTInterface)
    : CIRCTBuildM Nat := do
  let b ← get
  let name := if name.isEmpty then s!"inst{b.insts.size}" else name
  let newInsts := b.insts.push {name := name, ifc := ifc, inputs := fun _ => none}
  set {b with insts := newInsts }
  return b.insts.size

def CIRCTBuilder.defineInstInputPort
    (i p: Nat)
    {t : SignalType}
    (r : BuilderRef t)
    : CIRCTBuildM Unit := do
  let b ← get
  let checkedI ← checkedFin b.insts.size i
  let ports := b.insts[checkedI].ifc.ports
  let checkedP ← checkedFin ports.nInputs p
  let expectedType := ports.inputTypes checkedP
  let castR ← checkedCast expectedType r
  let inputs : BuilderRefs ports.inputTypes := fun port =>
    if h : checkedP = port then
      some (h ▸ castR)
    else
      b.insts[checkedI].inputs port
  let slot := b.insts[checkedI]
  set { b with
    insts := b.insts.set checkedI {slot with inputs := inputs}
  }

def CIRCTBuilder.defineOutput
    (p : Nat)
    {t : SignalType}
    (r : BuilderRef t)
    : CIRCTBuildM Unit := do
  let b ← get
  let checkedP ← checkedFin b.ifc.ports.nOutputs p
  let expectedType := b.ifc.ports.outputTypes checkedP
  let castR ← checkedCast expectedType r
  let outputs : BuilderRefs b.ifc.ports.outputTypes := fun port =>
    if hPort : checkedP = port then
      hPort ▸ some castR
    else
      b.outputs port
  set { b with outputs := outputs}

def finalizeRef
    (b : CIRCTBuilder)
    {t : SignalType}
    (ref : BuilderRef t)
    : Except String (Ref b.ctx t) :=
  match ref with
  | .exprRef index => do
    let checkedIndex ← checkedFin b.ctx.exprs.size index
    let newRef := Ref.exprRef (ctx := b.ctx) checkedIndex
    return ← checkedCast t newRef
  | .inputRef port => do
    let checkedPort ← checkedFin b.ifc.ports.nInputs port
    let newRef := Ref.inputRef (ctx := b.ctx) checkedPort
    return ← checkedCast t newRef
  | .instOutputRef inst port => do
    let checkedInst ← checkedFin b.ctx.insts.size inst
    let checkedPort ← checkedFin b.ctx.insts[checkedInst].ifc.ports.nOutputs port
    let newRef := Ref.instOutputRef (ctx := b.ctx) checkedInst checkedPort
    return ← checkedCast t newRef

def finalizeExpr
    (b : CIRCTBuilder)
    (i : Fin b.ctx.exprs.size)
    : Except String (Expr b.ctx b.ctx.exprs[i].type) :=
    have sizesEqual : b.ctx.exprs.size = b.exprs.size := by
      simp [CIRCTBuilder.ctx]
    let slotI : Fin b.exprs.size := i.cast sizesEqual
    have sameType : b.exprs[slotI].type = b.ctx.exprs[i].type := by
      change b.exprs[slotI.val].type = b.ctx.exprs[i.val].type
      simp [CIRCTBuilder.ctx, slotI]
    let impl : Option (BuilderExpr b.ctx.exprs[i].type) :=
      sameType ▸ b.exprs[i].impl
    match b.ctx.exprs[i].type, impl with
    | _, .none => do
      throw "No expr implementation"
    | _, .some (.constant value) => do
      return .constant value
    | _, .some (.ref ref) => do
      return .ref (← finalizeRef b ref)
    | _, .some (.reg next) => do
      return .reg (← finalizeRef b next)
    | _, .some (.add lhs rhs) => do
      return .add (← finalizeRef b lhs) (← finalizeRef b rhs)
    | _, .some (.sub lhs rhs) => do
      return .sub (← finalizeRef b lhs) (← finalizeRef b rhs)
    | _, .some (.mul lhs rhs) => do
      return .mul (← finalizeRef b lhs) (← finalizeRef b rhs)
    | _, .some (.extract value lowBit outputWidth inBounds) => do
      return .extract (← finalizeRef b value) lowBit outputWidth inBounds
    | _, .some (.concat high low) => do
      return .concat (← finalizeRef b high) (← finalizeRef b low)
    | _, .some (.replicate value count positive) => do
      return .replicate (← finalizeRef b value) count positive
    | _, .some (.structExtract value field) => do
      return .structExtract (← finalizeRef b value) field
    | _, .some (.structCreate values) => do
      let refs ← collect fun i => finalizeRef b (values i)
      return .structCreate refs

def finalizeExprImpls
    (b : CIRCTBuilder)
    : Except String (ExprImpls b.ctx) :=
  collect (finalizeExpr b)

def finalizeInstPort
    (b : CIRCTBuilder)
    (i : Fin b.ctx.insts.size)
    (p : b.ctx.insts[i].ifc.ports.InputKey)
    : Except String (Ref b.ctx (b.ctx.insts[i].ifc.ports.inputTypes p)) :=
  have sizesEqual : b.ctx.insts.size = b.insts.size := by
    simp [CIRCTBuilder.ctx]
  let slotI : Fin b.insts.size := i.cast sizesEqual
  have ifcEqual : b.insts[slotI].ifc = b.ctx.insts[i].ifc := by
    change b.insts[slotI.val].ifc = b.ctx.insts[i.val].ifc
    simp [CIRCTBuilder.ctx, slotI]
  let inputs : BuilderRefs b.ctx.insts[i].ifc.ports.inputTypes :=
    ifcEqual ▸ b.insts[slotI].inputs
  let ref := inputs p
  match ref with
  | none => throw "Instance input port not connected"
  | some ref => finalizeRef b ref

def finalizeInst
    (b : CIRCTBuilder)
    (i : Fin b.ctx.insts.size)
    : Except String (Refs b.ctx b.ctx.insts[i].ifc.ports.inputTypes) :=
    collect (finalizeInstPort b i)

def finalizeInstImpls
    (b : CIRCTBuilder)
    : Except String (InstImpls b.ctx) :=
    collect (finalizeInst b)

def finalizeOutput
    (b : CIRCTBuilder)
    (p : b.ifc.ports.OutputKey)
    : Except String (Ref b.ctx (b.ifc.ports.outputTypes p)) :=
  let output := b.outputs p
  match output with
  | none => throw "Instance output port not connected"
  | some ref => finalizeRef b ref

def finalizeOutputs
    (b : CIRCTBuilder)
    : Except String (OutputImpls b.ctx) :=
    collect (finalizeOutput b)

def CIRCTBuilder.finalize
    (b : CIRCTBuilder)
    : Except String CIRCTModule := do
  return {
    ifc := b.ifc,
    exprDecls := b.ctx.exprs
    instDecls := b.ctx.insts
    exprImpls := (← finalizeExprImpls b)
    instImpls := (← finalizeInstImpls b)
    outputs := (← finalizeOutputs b)
  }

def IfcFromImpl (impl : CIRCTImplementation ports) : Option CIRCTInterface :=
  match impl with
  | .primitive _ => none
  | .composite body naming children => some {
    ports := body.ports,
    naming := naming
  }

structure DesignState where
  mods : Std.HashMap ModuleKey CIRCTModule

abbrev DesignBuildM :=
  StateT DesignState (Except String)

def buildComposite
    (body : ModuleBody)
    (childBuilders : (childIndex : body.ChildKey) →
       CIRCTModuleBuilder (body.childPorts childIndex))
    : CIRCTModuleBuilder body.ports :=
  fun inputs => do
    let childRefs ← collect fun childIndex => do
      let childPorts := body.childPorts childIndex
      let inputRefs ← collect fun (port : childPorts.InputKey) => do
        return BuilderRef.exprRef (← CIRCTBuilder.declareExpr (childPorts.inputTypes port) "")
      let outputRefs ← (childBuilders childIndex) inputRefs
      return (inputRefs, outputRefs)
    let sourceRef {t : SignalType} : Source body.ports body.childPorts t → BuilderRef t
      | .input port => inputs port
      | .childOutput child port => (childRefs child).2 port
    for childIndex in List.finRange body.nChildren do
      for inputKey in List.finRange (body.childPorts childIndex).nInputs do
        let driver := sourceRef (body.childInputDrivers childIndex inputKey)
        match (childRefs childIndex).1 inputKey with
        | .exprRef index => CIRCTBuilder.defineExpr index (.ref driver)
        | _ => throw "Child input is not an expression slot"
    return fun outputKey => sourceRef (body.outputDrivers outputKey)

def buildModule
    (ifc : CIRCTInterface)
    (builder : CIRCTModuleBuilder ifc.ports)
    : Except String CIRCTModule := do
  let action : CIRCTBuildM Unit := do
    let inputRefs := fun (port : ifc.ports.InputKey) =>
      BuilderRef.inputRef port.val
    let outputRefs ← builder inputRefs
    for port in List.finRange ifc.ports.nOutputs do
      CIRCTBuilder.defineOutput port.val (outputRefs port)
  let initial : CIRCTBuilder := {
    ifc,
    exprs := #[],
    insts := #[],
    outputs := fun _ => none,

}
  let (_, builder) ← action.run initial
  builder.finalize

def buildImplementation
    (settings : CIRCTSettings)
    (registry : Registry)
    {ports : ModulePorts}
    (path : List ModuleKey)
    (implRef : ModuleRef ports)
    : DesignBuildM (CIRCTModuleBuilder ports) := do
  let implKey := implRef.toModuleKey
  if path.length >= settings.maxDepth then
    throw "Max recursion depth exceeded"
  else
    let impl ← registry.resolve settings implRef
    return ← (match
      (motive := (p : ModulePorts) → CIRCTImplementation p → DesignBuildM (CIRCTModuleBuilder p))
      ports, impl with
      | _, .primitive builder =>
        return builder
      | _, .composite body naming children => do
        let s ← get
        -- Build the composite child modules if not already done
        if path.contains implKey then
          throw "Circular module reference"
        if !s.mods.contains implKey then
          let updatedPath := path.append [implKey]
          let childBuilders ← collect fun (i : body.ChildKey) =>
            buildImplementation settings registry updatedPath (children i settings)
          let builder := buildComposite body childBuilders
          let ifc : CIRCTInterface := {
            ports := body.ports,
            naming := naming,
          }
          let mod ← buildModule ifc builder
          modify fun s => {s with mods := s.mods.insert implKey mod}
        -- Make the builder for this composite module
        let ifc : CIRCTInterface := {
          ports := body.ports,
          naming := naming,
        }
        let builder : CIRCTModuleBuilder body.ports := fun inputRefs => do
          let instRef ← CIRCTBuilder.declareInst "" ifc
          for port in List.finRange body.ports.nInputs do
            CIRCTBuilder.defineInstInputPort instRef port (inputRefs port)
          let outputRefs := fun port : body.ports.OutputKey =>
            BuilderRef.instOutputRef instRef port
          return outputRefs
        return builder
    )
  termination_by settings.maxDepth - path.length
  decreasing_by
    simp_all
    omega

def buildDesign
    (settings : CIRCTSettings)
    (registry : Registry)
    {ports : ModulePorts}
    (implRef : ModuleRef ports)
    : Except String (Std.HashMap ModuleKey CIRCTModule) := do
  let action : DesignBuildM Unit := do
    let _ ← buildImplementation settings registry [] implRef
    pure ()
  let (_, state) ← action.run {
    mods := {}
  }
  return state.mods

end Silean2.CIRCT
