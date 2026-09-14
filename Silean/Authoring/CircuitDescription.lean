import Silean.Naming.ModuleNaming

/-! A checked-translation boundary, not a replacement structural semantics.
Descriptions retain actual named children; equality therefore checks more than
module keys or interfaces. Lists also preserve declaration order. Authoring nets
are symbolic references: their validity is established by matching the complete
description extracted from a typed production body, not by trusting the builder.
-/
namespace Silean.Authoring.CircuitDescription

open Silean Naming

/-- Naming transported between equal structures at the same interface keeps
its port names. The explicit structure equality also handles opaque equality
proofs emitted by production's naming definitions. -/
theorem ports_mpr_of_eq {ports : ModulePorts} {left right : ModuleStructure ports}
    (equal : left = right) (typeEqual : ModuleNaming left = ModuleNaming right)
    (naming : ModuleNaming right) :
    (typeEqual.mpr naming).ports = naming.ports := by
  cases equal
  rfl

structure Port where
  name : SourceName
  signalType : SignalType

inductive Source where
  | input (name : SourceName)
  | child (instanceName portName : SourceName)
deriving DecidableEq, Repr

structure Connection where
  port : Port
  source : Source

structure Child where
  name : SourceName
  module : NamedModule
  inputs : List Connection

structure Description where
  inputs : List Port := []
  outputs : List Connection := []
  children : List Child := []

def portList (signals : SignalMap) (names : SignalMapNaming signals) : List Port :=
  signals.labels.values.map fun label => ⟨names.name label, signals.signalType label⟩

def sourceDescription {body : ModuleBody}
    (ports : ModulePortsNaming body.ports)
    (instanceName : body.instancePorts.Name → SourceName)
    (childPorts : (child : body.instancePorts.Name) →
      ModulePortsNaming (body.instancePorts.ports child)) :
    SignalSource body.ports body.instancePorts signalType → Source
  | .moduleInput port => .input (ports.inputs.name port)
  | .instanceOutput child port => .child (instanceName child)
      ((childPorts child).outputs.name port)

/-- Extract every boundary port, child, and driven sink from the actual body.
The child structures and their naming come from the composite's naming witness. -/
def ofNaming {modulePorts : ModulePorts} {moduleStructure : ModuleStructure modulePorts} :
    ModuleNaming moduleStructure → Option Description
  | .composite (body := body) (children := children) _ ports instanceName childNaming =>
    let source := fun {signalType} => sourceDescription (body := body)
      ports instanceName (fun child => (childNaming child).ports) (signalType := signalType)
    some <|
    { inputs := portList body.ports.inputs ports.inputs
      outputs := body.ports.outputs.labels.values.map fun port =>
        ⟨⟨ports.outputs.name port, body.ports.outputs.signalType port⟩,
          source (body.wiring.moduleOutput port)⟩
      children := body.instancePorts.names.values.map fun child =>
        { name := instanceName child
          module := ⟨body.instancePorts.ports child, children child, childNaming child⟩
          inputs := (body.instancePorts.ports child).inputs.labels.values.map fun port =>
            ⟨⟨(childNaming child).ports.inputs.name port,
                (body.instancePorts.ports child).inputs.signalType port⟩,
              source (body.wiring.instanceInput child port)⟩ } }
  | _ => none

/-- Unique names at each namespace prevent erasure from merging labels.
Child port uniqueness covers outputs too, including unused outputs. -/
def Description.UniqueNames (description : Description) : Prop :=
  ((description.inputs.map (·.name)) ++
    (description.outputs.map (·.port.name))).Nodup ∧
  (description.children.map (·.name)).Nodup ∧
  ∀ child ∈ description.children,
    child.module.naming.ports.names.Nodup ∧
    (child.inputs.map (·.port.name)).Nodup

/-- The per-module certificate checks the translation, not hardware behavior. -/
structure Corresponds {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    (description : Description) (naming : ModuleNaming (.composite body children)) : Prop where
  same : some description = ofNaming naming
  unique : description.UniqueNames

structure Net (signalType : SignalType) where
  source : Source

/-- A universe-polymorphic-state builder with ordinary small result types. -/
def Builder (α : Type) : Type 1 := Description → α × Description

instance : Monad Builder where
  pure value := fun state => (value, state)
  bind action next := fun state =>
    let (value, state) := action state
    next value state

def build (action : Builder Unit) : Description := (action {}).2

def input (name : SourceName) (signalType : SignalType) : Builder (Net signalType) :=
  fun state => (⟨.input name⟩, { state with inputs := state.inputs ++ [⟨name, signalType⟩] })

def output (name : SourceName) (net : Net signalType) : Builder Unit :=
  fun state => ((), { state with outputs := state.outputs ++ [⟨⟨name, signalType⟩, net.source⟩] })

/-- Place an existing production child, preserving its full identity. -/
def place (name : SourceName) (module : NamedModule)
    (inputs : (port : module.ports.inputs.Label) → Net (module.ports.inputs.signalType port)) :
    Builder ((port : module.ports.outputs.Label) → Net (module.ports.outputs.signalType port)) :=
  fun state =>
    (fun port => ⟨.child name (module.naming.ports.outputs.name port)⟩,
      { state with children := state.children ++
          [{ name := name
             module := module
             inputs := module.ports.inputs.labels.values.map fun port =>
               ⟨⟨module.naming.ports.inputs.name port, module.ports.inputs.signalType port⟩,
                 (inputs port).source⟩ }] })

end Silean.Authoring.CircuitDescription
