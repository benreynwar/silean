import Lean
import Silean2.FoundationsH
import Silean2.CIRCT.ModelH

namespace Silean2.CIRCT

open Silean2.Foundations

structure CIRCTSettings where
  maxDepth : Nat
  deriving Lean.FromJson

inductive BuilderRef (t : SignalType) : Type
  | exprRef (exprIndex : Nat) : BuilderRef t
  | inputRef (inputIndex : Nat) : BuilderRef t
  | instOutputRef (instIndex : Nat)
    (nodeOutputIndex : Nat) : BuilderRef t

inductive BuilderExpr : SignalType → Type
  | constant {t : SignalType} (value : t.Denote) : BuilderExpr t
  | ref {t : SignalType} (ref : BuilderRef t) : BuilderExpr t
  | reg {t : SignalType} (next : BuilderRef t) : BuilderExpr t
  | add {width : Nat} (lhs : BuilderRef (CIRCTInt width))
      (rhs : BuilderRef (CIRCTInt width))
    : BuilderExpr (CIRCTInt width)
  | sub {width : Nat} (lhs : BuilderRef (CIRCTInt width)) (rhs : BuilderRef (CIRCTInt width))
    : BuilderExpr (CIRCTInt width)
  | mul {width : Nat} (lhs : BuilderRef (CIRCTInt width)) (rhs : BuilderRef (CIRCTInt width))
    : BuilderExpr (CIRCTInt width)
  | extract {inputWidth : Nat}
      (value : BuilderRef (CIRCTInt inputWidth))
      (lowBit outputWidth : Nat)
      (inBounds : lowBit + outputWidth ≤ inputWidth)
    : BuilderExpr (CIRCTInt outputWidth)
  | concat {highWidth lowWidth : Nat}
      (high : BuilderRef (CIRCTInt highWidth)) (low : BuilderRef (CIRCTInt lowWidth))
    : BuilderExpr (CIRCTInt (highWidth + lowWidth))
  | replicate {inputWidth: Nat}
      (value : BuilderRef (CIRCTInt inputWidth))
      (count : Nat) (positive : 0 < count)
    : BuilderExpr (CIRCTInt (inputWidth * count))
  | structExtract {fields : SignalTypes}
      (value : BuilderRef (.tuple fields))
      (field : Fin fields.length)
    : BuilderExpr (fields.get field)
  | structCreate {fields : SignalTypes}
      (values : (i : Fin fields.length) → BuilderRef (fields.get i))
    : BuilderExpr (.tuple fields)

abbrev BuilderRefs {nPorts : Nat} (types : PortTypes nPorts) :=
  (i : Fin nPorts) → Option (BuilderRef (types i))

structure ExprSlot where
  name : String
  type : SignalType
  impl : Option (BuilderExpr type)

structure InstSlot where
  name : String
  ifc : CIRCTInterface
  inputs : BuilderRefs ifc.ports.inputTypes

structure CIRCTBuilder where
  ifc : CIRCTInterface
  exprs : Array ExprSlot
  insts : Array InstSlot
  outputs : BuilderRefs ifc.ports.outputTypes

def CIRCTBuilder.ctx (b : CIRCTBuilder) : Context :=
  {
    ifc := b.ifc,
    exprs := (b.exprs.map fun e =>
      {name := e.name, type := e.type})
    insts := (b.insts.map fun inst =>
      {name := inst.name, ifc := inst.ifc})
  }

abbrev CIRCTBuildM := StateT CIRCTBuilder (Except String)

def CIRCTModuleBuilder (ports : ModulePorts) :=
  ((i : ports.InputKey ) → BuilderRef (ports.inputTypes i)) →
  CIRCTBuildM ((o : ports.OutputKey) → BuilderRef (ports.outputTypes o))

mutual
  inductive RawParamsType where
    | nat
    | bool
    | vector (element : RawParamsType) (length : Nat)
    | record (fields : RawParamsFields)
    deriving DecidableEq, Hashable

  inductive RawParamsFields where
    | nil
    | cons (name : String) (type : RawParamsType) (rest : RawParamsFields)
end

syntax "params%[" (str " : " term),*,? "]" : term

macro_rules
  | `(params%[$[$names: str : $types:term],*]) => do
    let mut fields ← `(Silean2.CIRCT.RawParamsFields.nil)
    for i in [:names.size] do
      let j := names.size - i - 1
      fields ← `(Silean2.CIRCT.RawParamsFields.cons $(names[j]!) $(types[j]!) $fields)
    `(Silean2.CIRCT.RawParamsType.record $fields)

mutual
  def RawParamsType.Denote : RawParamsType → Type
    | .nat => Nat
    | .bool => Bool
    | .vector element length => Vector element.Denote length
    | .record fields => fields.Denote

  def RawParamsFields.Denote : RawParamsFields → Type
    | .nil => Unit
    | .cons _ type rest => type.Denote × rest.Denote

end

mutual
  @[implicit_reducible]
  def RawParamsType.denoteHashable : (t : RawParamsType) → Hashable t.Denote
    | .nat => inferInstanceAs (Hashable Nat)
    | .bool => inferInstanceAs (Hashable Bool)
    | .vector element _ =>
        letI := element.denoteHashable
        { hash := fun values => hash values.toArray }
    | .record fields => fields.denoteHashable

  @[implicit_reducible]
  def RawParamsFields.denoteHashable : (t : RawParamsFields) → Hashable t.Denote
    | .nil => inferInstanceAs (Hashable Unit)
    | .cons _ type rest =>
        letI := type.denoteHashable
        letI := rest.denoteHashable
        inferInstanceAs (Hashable (type.Denote × rest.Denote))
end

instance (t : RawParamsType) : Hashable t.Denote := t.denoteHashable
instance (t : RawParamsFields) : Hashable t.Denote := t.denoteHashable

mutual
  def RawParamsType.denoteDecidableEq :
      (t : RawParamsType) → DecidableEq t.Denote
    | .nat => inferInstanceAs (DecidableEq Nat)
    | .bool => inferInstanceAs (DecidableEq Bool)
    | .vector element length =>
        letI := element.denoteDecidableEq
        inferInstanceAs (DecidableEq (Vector element.Denote length))
    | .record fields => fields.denoteDecidableEq

  def RawParamsFields.denoteDecidableEq :
      (t : RawParamsFields) → DecidableEq t.Denote
    | .nil => inferInstanceAs (DecidableEq Unit)
    | .cons _ type rest =>
        letI := type.denoteDecidableEq
        letI := rest.denoteDecidableEq
        inferInstanceAs (DecidableEq (type.Denote × rest.Denote))
end

instance (t : RawParamsType) : DecidableEq t.Denote :=
  t.denoteDecidableEq

structure ModuleKey where
  name : String
  paramsType : RawParamsType
  params : paramsType.Denote
  deriving DecidableEq, Hashable

instance : BEq ModuleKey where
  beq a b := decide (a = b)

structure ModuleRef (ports : ModulePorts) extends ModuleKey

inductive CIRCTImplementation : ModulePorts → Type where
  | primitive
      {ports : ModulePorts}
      (build : CIRCTModuleBuilder ports)
      : CIRCTImplementation ports
  | composite
      (body : ModuleBody)
      (naming : CIRCTNaming body.ports)
      (children : (i : body.ChildKey) → CIRCTSettings →
        ModuleRef (body.childPorts i))
      : CIRCTImplementation body.ports

def CIRCTImplementation.ports {ports : ModulePorts}
    (impl: CIRCTImplementation ports) : ModulePorts :=
  match impl with
  | .primitive _ => ports
  | .composite _ _ _ => ports

structure ModuleSigRegistration where
  Params : Type
  paramsEq : DecidableEq Params
  paramsHash : Hashable Params
  ports : Params → ModulePorts

structure ModuleRegistration where
  rawParamsType : RawParamsType
  ParamsType : Type
  decodeParams : rawParamsType.Denote → Except String ParamsType
  ports : ParamsType → ModulePorts
  impl : (params : ParamsType) → CIRCTSettings → CIRCTImplementation (ports params)

abbrev Registry := Std.HashMap String ModuleRegistration

def Registry.register (r : Registry) (name : String) (m : ModuleRegistration)
    : Except String Registry :=
  if name ∈ r then
    throw "name {m.name} is already registered"
  else
    pure (r.insert name m)

def Registry.resolve
    (registry : Registry)
    (settings : CIRCTSettings)
    {ports : ModulePorts}
    (ref : ModuleRef ports)
    : Except String (CIRCTImplementation ports) := do
  let some registration := registry[ref.name]?
    | throw s!"Module {ref.name} not found inregistry"
  if hParams : ref.paramsType = registration.rawParamsType then
    let rawParams : registration.rawParamsType.Denote :=
      hParams ▸ ref.params
    let params : registration.ParamsType ← registration.decodeParams rawParams
    if hPorts : registration.ports params = ports then
      let impl : CIRCTImplementation ports :=
        hPorts ▸ registration.impl params settings
      return impl
    else
      throw s!"Port mismatch for module {ref.name}"
  else
      throw s!"Params type mismatch for module {ref.name}"

def Registry.empty : Registry := {}

end Silean2.CIRCT
