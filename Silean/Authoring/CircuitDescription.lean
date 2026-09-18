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

/-- Extract every boundary port, child, and driven sink from a composite's
naming witness. -/
@[reducible] def ofCompositeNaming {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    (ports : ModulePortsNaming body.ports)
    (instanceName : body.instancePorts.Name → SourceName)
    (childNaming : (child : body.instancePorts.Name) →
      ModuleNaming (children child)) : Description :=
  let source := fun {signalType} => sourceDescription (body := body)
    ports instanceName (fun child => (childNaming child).ports) (signalType := signalType)
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

/-- Extract a description from a composite naming. Primitive and adapter
namings do not contain a child hierarchy and therefore return `none`. -/
def ofNaming {modulePorts : ModulePorts} {moduleStructure : ModuleStructure modulePorts} :
    ModuleNaming moduleStructure → Option Description
  | .composite _ ports instanceName childNaming =>
      some (ofCompositeNaming ports instanceName childNaming)
  | _ => none

@[simp] theorem ofNaming_composite {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    (key : ModuleKey) (ports : ModulePortsNaming body.ports)
    (instanceName : body.instancePorts.Name → SourceName)
    (childNaming : (child : body.instancePorts.Name) →
      ModuleNaming (children child)) :
    ofNaming (ModuleNaming.composite key ports instanceName childNaming) =
      some (ofCompositeNaming ports instanceName childNaming) := rfl

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

/-! ## Draft construction

`Description` remains the resolved, checked-translation boundary used by the
soundness development above. The builder works in a separate draft language so
authors may declare a typed wire before its driver is available. Finalization
eliminates every such wire; neither `Description` nor structural semantics has
an unresolved-wire case. -/

inductive NetOrigin where
  | source (source : Source)
  | wire (id : Nat)
deriving DecidableEq, Repr

/-- An author-facing typed reference to either a resolved source or a draft wire. -/
structure Net (signalType : SignalType) where
  origin : NetOrigin
deriving DecidableEq, Repr

structure DraftConnection where
  port : Port
  driver : Net port.signalType

structure DraftChild where
  name : SourceName
  module : NamedModule
  inputs : List DraftConnection

structure WireDraft where
  id : Nat
  name : SourceName
  signalType : SignalType
  drivers : List (Net signalType)

/-- Failures detected while assigning or resolving authoring-only wires. -/
inductive BuildError where
  | assignmentTargetNotWire
  | unknownWire (id : Nat)
  | wireTypeMismatch (name : SourceName)
  | duplicateWireName
  | undrivenWire (name : SourceName)
  | multiplyDrivenWire (name : SourceName)
  | wireAliasCycle
deriving DecidableEq, Repr

structure Draft where
  inputs : List Port := []
  outputs : List DraftConnection := []
  children : List DraftChild := []
  wires : List WireDraft := []
  errors : List BuildError := []
  nextWire : Nat := 0

/-- A universe-polymorphic-state builder with ordinary small result types. -/
def Builder (α : Type) : Type 1 := Draft → α × Draft

instance : Monad Builder where
  pure value := fun state => (value, state)
  bind action next := fun state =>
    let (value, state) := action state
    next value state

@[simp] theorem bind_apply (action : Builder α) (next : α → Builder β)
    (state : Draft) :
    (action >>= next) state =
      (match action state with | (value, state) => next value state) := by
  rfl

@[simp] theorem pure_apply (value : α) (state : Draft) :
    (pure value : Builder α) state = (value, state) := by
  rfl

namespace Internal

def findWire? (id : Nat) : List WireDraft → Option WireDraft
  | [] => none
  | wire :: rest => if wire.id = id then some wire else findWire? id rest

def replaceWire (id : Nat) (replacement : WireDraft) :
    List WireDraft → List WireDraft
  | [] => []
  | wire :: rest =>
      if wire.id = id then replacement :: rest
      else wire :: replaceWire id replacement rest

def validateWireDrivers : List WireDraft → Except BuildError Unit
  | [] => .ok ()
  | wire :: rest =>
      match wire.drivers with
      | [] => .error (.undrivenWire wire.name)
      | [_] => validateWireDrivers rest
      | _ => .error (.multiplyDrivenWire wire.name)

def resolveNet (wires : List WireDraft) :
    (fuel : Nat) → {signalType : SignalType} → Net signalType →
      Except BuildError Source
  | 0, _, _ => .error .wireAliasCycle
  | fuel + 1, signalType, net =>
      match net.origin with
      | .source source => .ok source
      | .wire id =>
          match findWire? id wires with
          | none => .error (.unknownWire id)
          | some wire =>
              if same : wire.signalType = signalType then
                match wire.drivers with
                | [driver] => resolveNet wires fuel (same ▸ driver)
                | [] => .error (.undrivenWire wire.name)
                | _ => .error (.multiplyDrivenWire wire.name)
              else
                .error (.wireTypeMismatch wire.name)

/-- Check that every declared wire ultimately reaches an input or child
output, including wires which happen not to feed a boundary or child sink. -/
def validateWireSources (wires : List WireDraft) :
    List WireDraft → Except BuildError Unit
  | [] => .ok ()
  | wire :: rest =>
      match resolveNet wires (wires.length + 1)
          ({ origin := .wire wire.id } : Net wire.signalType) with
      | .error error => .error error
      | .ok _ => validateWireSources wires rest

def finalizeConnection (wires : List WireDraft)
    (connection : DraftConnection) : Except BuildError Connection :=
  match resolveNet wires (wires.length + 1) connection.driver with
  | .ok source => .ok ⟨connection.port, source⟩
  | .error error => .error error

def finalizeConnections (wires : List WireDraft) :
    List DraftConnection → Except BuildError (List Connection)
  | [] => .ok []
  | connection :: rest =>
      match finalizeConnection wires connection with
      | .error error => .error error
      | .ok resolved =>
          match finalizeConnections wires rest with
          | .error error => .error error
          | .ok resolvedRest => .ok (resolved :: resolvedRest)

def finalizeChild (wires : List WireDraft)
    (child : DraftChild) : Except BuildError Child :=
  match finalizeConnections wires child.inputs with
  | .error error => .error error
  | .ok inputs => .ok { name := child.name, module := child.module, inputs := inputs }

def finalizeChildren (wires : List WireDraft) :
    List DraftChild → Except BuildError (List Child)
  | [] => .ok []
  | child :: rest =>
      match finalizeChild wires child with
      | .error error => .error error
      | .ok resolved =>
          match finalizeChildren wires rest with
          | .error error => .error error
          | .ok resolvedRest => .ok (resolved :: resolvedRest)

def finalizeDraft (draft : Draft) : Except BuildError Description :=
  match draft.errors with
  | error :: _ => .error error
  | [] =>
      if _unique : (draft.wires.map (fun wire => wire.name)).Nodup then
        match validateWireDrivers draft.wires with
        | .error error => .error error
        | .ok _ =>
          match validateWireSources draft.wires draft.wires with
          | .error error => .error error
          | .ok _ =>
            match finalizeConnections draft.wires draft.outputs with
            | .error error => .error error
            | .ok outputs =>
                match finalizeChildren draft.wires draft.children with
                | .error error => .error error
                | .ok children => .ok
                    { inputs := draft.inputs, outputs := outputs, children := children }
      else
        .error .duplicateWireName

/-- Sentinel returned by the convenience `build` projection on failure. Its
duplicate boundary names make `Description.UniqueNames` unprovable, so it
cannot acquire a production correspondence certificate. -/
def invalidDescription : Description :=
  { inputs := [⟨"__invalid_build__", .bit⟩, ⟨"__invalid_build__", .bit⟩] }

theorem invalidDescription_not_unique : ¬ invalidDescription.UniqueNames := by
  intro unique
  simpa [invalidDescription] using unique.1

end Internal

/-- Run and validate an authoring construction without discarding diagnostics. -/
def buildResult (action : Builder Unit) : Except BuildError Description :=
  Internal.finalizeDraft (action {}).2

/-- Finalize a construction. On failure this returns a deliberately invalid
sentinel which cannot satisfy `Corresponds.unique`; use `buildResult` directly
when diagnostics are needed. -/
def build (action : Builder Unit) : Description :=
  match buildResult action with
  | .ok description => description
  | .error _ => Internal.invalidDescription

def input (name : SourceName) (signalType : SignalType) : Builder (Net signalType) :=
  fun state => (⟨.source (.input name)⟩,
    { state with inputs := state.inputs ++ [⟨name, signalType⟩] })

def output (name : SourceName) (net : Net signalType) : Builder Unit :=
  fun state => ((), { state with outputs := state.outputs ++
    [{ port := ⟨name, signalType⟩, driver := net }] })

/-- Declare a typed authoring wire whose driver may be assigned later. -/
def wire (name : SourceName) (signalType : SignalType) : Builder (Net signalType) :=
  fun state =>
    let id := state.nextWire
    (⟨.wire id⟩,
      { state with
        wires := state.wires ++
          [{ id := id, name := name, signalType := signalType, drivers := [] }]
        nextWire := id + 1 })

/-- Give a previously declared wire a driver. Destination comes first, as in a
Verilog continuous assignment. Finalization rejects missing or multiple
drivers. -/
def assign (target driver : Net signalType) : Builder Unit :=
  fun state =>
    match target.origin with
    | .source _ => ((), { state with
        errors := state.errors ++ [.assignmentTargetNotWire] })
    | .wire id =>
        match Internal.findWire? id state.wires with
        | none => ((), { state with errors := state.errors ++ [.unknownWire id] })
        | some targetWire =>
            if same : targetWire.signalType = signalType then
              let typedDriver : Net targetWire.signalType := same ▸ driver
              let replacement :=
                { targetWire with drivers := targetWire.drivers ++ [typedDriver] }
              ((), { state with
                wires := Internal.replaceWire id replacement state.wires })
            else
              ((), { state with
                errors := state.errors ++ [.wireTypeMismatch targetWire.name] })

/-- Place an existing production child under an explicit instance name,
preserving its full identity. -/
def placeNamed (name : SourceName) (module : NamedModule)
    (inputs : (port : module.ports.inputs.Label) → Net (module.ports.inputs.signalType port)) :
    Builder ((port : module.ports.outputs.Label) → Net (module.ports.outputs.signalType port)) :=
  fun state =>
    (fun port => ⟨.source (.child name (module.naming.ports.outputs.name port))⟩,
      { state with children := state.children ++
          [{ name := name
             module := module
             inputs := module.ports.inputs.labels.values.map fun port =>
               { port := ⟨module.naming.ports.inputs.name port,
                   module.ports.inputs.signalType port⟩
                 driver := inputs port } }] })

private def indexedInstanceCount (stem : String) : List DraftChild → Nat
  | [] => 0
  | child :: children =>
      (match child.name with
        | .indexed other _ => if other = stem then 1 else 0
        | _ => 0) + indexedInstanceCount stem children

/-- Place an existing production child using a conventional stem and its
occurrence number as a deterministic instance name. Module-specific helpers
supply the stem, so their callers do not manually name each instance. An
indexed name with stem `mask`, for example, emits as `mask_0`. -/
def placeIndexed (stem : String) (module : NamedModule)
    (inputs : (port : module.ports.inputs.Label) → Net (module.ports.inputs.signalType port)) :
    Builder ((port : module.ports.outputs.Label) → Net (module.ports.outputs.signalType port)) :=
  fun state =>
    placeNamed (.indexed stem (indexedInstanceCount stem state.children)) module inputs state

end Silean.Authoring.CircuitDescription
