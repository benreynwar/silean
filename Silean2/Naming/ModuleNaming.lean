import Silean2.Structure.ModuleStructure
import Silean2.Primitives

namespace Silean2.Naming

open Silean2

/-! Hardware names are ordinary executable metadata. Legality and collisions
are checked while collecting a FIRRTL circuit, not carried as theorem fields. -/

inductive SourceName where
  | plain (value : String)
  | indexed (stem : String) (index : Nat)
  | scoped (scope : String) (name : SourceName)
deriving DecidableEq, Repr

instance : Coe String SourceName := ⟨.plain⟩

mutual
  inductive SignalTypeNaming : (signalType : SignalType) → Type
    | bit : SignalTypeNaming .bit
    | vector (element : SignalTypeNaming elementType) :
        SignalTypeNaming (.vector length elementType)
    | tuple (fields : SignalTypesNaming fieldTypes) :
        SignalTypeNaming (.tuple fieldTypes)

  inductive SignalTypesNaming : (signalTypes : SignalTypes) → Type
    | nil : SignalTypesNaming .nil
    | cons (name : SourceName) (head : SignalTypeNaming headType)
        (tail : SignalTypesNaming tailTypes) :
        SignalTypesNaming (.cons headType tailTypes)
end

def SignalTypesNaming.typeAt : (naming : SignalTypesNaming signalTypes) →
    (position : SignalTypes.Position signalTypes) →
      SignalTypeNaming (signalTypes.typeAt position)
  | .cons _ head _, .head => head
  | .cons _ _ tail, .tail position => tail.typeAt position

def SignalTypesNaming.nameAt : SignalTypesNaming signalTypes →
    SignalTypes.Position signalTypes → SourceName
  | .cons name _ _, .head => name
  | .cons _ _ tail, .tail position => tail.nameAt position

def SignalTypeNaming.component : (naming : SignalTypeNaming signalType) →
    (component : match signalType with
      | .bit => PEmpty
      | .vector length _ => Fin length
      | .tuple fields => SignalTypes.Position fields) →
    SignalTypeNaming (match signalType with
      | .bit => nomatch component
      | .vector _ element => element
      | .tuple fields => fields.typeAt component)
  | .vector element, _ => element
  | .tuple fields, component => fields.typeAt component

mutual
  def SignalTypeNaming.positional : (signalType : SignalType) →
      SignalTypeNaming signalType
    | .bit => .bit
    | .vector _ element => .vector (SignalTypeNaming.positional element)
    | .tuple fields => .tuple (SignalTypesNaming.positional fields 0)

  def SignalTypesNaming.positional : (signalTypes : SignalTypes) → Nat →
      SignalTypesNaming signalTypes
    | .nil, _ => .nil
    | .cons head tail, index =>
        .cons (.plain s!"_{index}") (SignalTypeNaming.positional head)
          (SignalTypesNaming.positional tail (index + 1))
end

inductive ModuleParameter where
  | natural (value : Nat)
  | shape (signalType : SignalType)
deriving DecidableEq, Repr

structure ModuleKey where
  family : String
  variant : String
  specialization : List ModuleParameter := []
deriving DecidableEq, Repr

structure SignalMapNaming (signals : SignalMap) where
  name : signals.Label → SourceName

def SignalMapNaming.names (naming : SignalMapNaming signals) : List SourceName :=
  signals.labels.values.map naming.name

private def listIndexToNat : ListIndex value values → Nat
  | .head => 0
  | .tail index => listIndexToNat index + 1

def SignalMapNaming.indexed (signals : SignalMap) (stem : String) :
    SignalMapNaming signals :=
  ⟨fun label => .indexed stem (listIndexToNat (signals.labels.locate label))⟩

structure ModulePortsNaming (ports : ModulePorts) where
  inputs : SignalMapNaming ports.inputs
  outputs : SignalMapNaming ports.outputs
  inputTypes : (label : ports.inputs.Label) →
    SignalTypeNaming (ports.inputs.signalType label) :=
      fun label => SignalTypeNaming.positional (ports.inputs.signalType label)
  outputTypes : (label : ports.outputs.Label) →
    SignalTypeNaming (ports.outputs.signalType label) :=
      fun label => SignalTypeNaming.positional (ports.outputs.signalType label)

def ModulePortsNaming.names (naming : ModulePortsNaming ports) : List SourceName :=
  naming.inputs.names ++ naming.outputs.names

/-! This is the one type-safe part of primitive emission metadata: an arbitrary
open `Primitive` cannot be mislabeled as a supported FIRRTL operation. -/

inductive PrimitiveOperation : (primitive : Primitive) → Type
  | not : PrimitiveOperation Primitives.not
  | and : PrimitiveOperation Primitives.and
  | or : PrimitiveOperation Primitives.or
  | xor : PrimitiveOperation Primitives.xor
  | eq : PrimitiveOperation Primitives.eq
  | register : PrimitiveOperation Primitives.register
  | constant (value : Bool) : PrimitiveOperation (Primitives.constant value)

inductive ModuleNaming : {ports : ModulePorts} → ModuleStructure ports → Type 1
  | primitive {primitive : Primitive}
      (key : ModuleKey)
      (ports : ModulePortsNaming primitive.ports)
      (state : SignalMapNaming primitive.localState)
      (operation : PrimitiveOperation primitive) :
      ModuleNaming (.primitive primitive)
  | splitter (splitter : SignalSplitter)
      (key : ModuleKey) (ports : ModulePortsNaming splitter.ports) :
      ModuleNaming (.splitter splitter)
  | combiner (combiner : SignalCombiner)
      (key : ModuleKey) (ports : ModulePortsNaming combiner.ports) :
      ModuleNaming (.combiner combiner)
  | composite {body : ModuleBody}
      {children : (name : body.context.instances.Name) →
        ModuleStructure (body.context.instances.ports name)}
      (key : ModuleKey)
      (ports : ModulePortsNaming body.context.ports)
      (instanceName : body.context.instances.Name → SourceName)
      (childNaming : (name : body.context.instances.Name) →
        ModuleNaming (children name)) :
      ModuleNaming (.composite body children)

namespace ModuleNaming

def key : ModuleNaming moduleStructure → ModuleKey
  | .primitive key _ _ _ => key
  | .splitter _ key _ => key
  | .combiner _ key _ => key
  | .composite key _ _ _ => key

def ports {modulePorts : ModulePorts}
    {moduleStructure : ModuleStructure modulePorts} :
    ModuleNaming moduleStructure → ModulePortsNaming modulePorts
  | .primitive _ ports _ _ => ports
  | .splitter _ _ ports => ports
  | .combiner _ _ ports => ports
  | .composite _ ports _ _ => ports

def withKey (newKey : ModuleKey) :
    (naming : ModuleNaming moduleStructure) → ModuleNaming moduleStructure
  | .primitive _ ports state operation => .primitive newKey ports state operation
  | .splitter adapter _ ports => .splitter adapter newKey ports
  | .combiner adapter _ ports => .combiner adapter newKey ports
  | .composite _ ports instanceName childNaming =>
      .composite newKey ports instanceName childNaming

def withPorts {modulePorts : ModulePorts}
    (newPorts : ModulePortsNaming modulePorts) :
    {moduleStructure : ModuleStructure modulePorts} →
      (naming : ModuleNaming moduleStructure) → ModuleNaming moduleStructure
  | _, .primitive key _ state operation => .primitive key newPorts state operation
  | _, .splitter adapter key _ => .splitter adapter key newPorts
  | _, .combiner adapter key _ => .combiner adapter key newPorts
  | _, .composite key _ instanceName childNaming =>
      .composite key newPorts instanceName childNaming

end ModuleNaming

structure NamedModule where
  ports : ModulePorts
  moduleStructure : ModuleStructure ports
  naming : ModuleNaming moduleStructure

def NamedModule.key (module : NamedModule) : ModuleKey := module.naming.key

end Silean2.Naming
