import Lean
import Silean.Authoring.CircuitDescriptionAttributes
import Silean.Naming.ModuleNaming

/-! A checked-translation boundary, not a replacement structural semantics.
Descriptions retain canonical description-local endpoint identities as well as
reader-facing names and actual child modules. Equality therefore checks more
than module keys or interfaces without treating emitted names as semantic keys.
Lists also preserve declaration order. Authoring nets are symbolic references:
their validity is established by matching the complete description extracted
from a typed production body, not by trusting the builder.
-/

namespace Silean.Authoring.CircuitDescription

open Silean Naming

structure PortId where
  index : Nat
deriving DecidableEq, Repr

structure ChildId where
  index : Nat
deriving DecidableEq, Repr

structure Port where
  id : PortId
  name : SourceName
  signalType : SignalType

inductive Source where
  | input (port : PortId)
  | child (child : ChildId) (port : PortId)
deriving DecidableEq, Repr

structure Connection where
  port : Port
  source : Source

structure Child where
  id : ChildId
  name : SourceName
  module : NamedModule
  inputs : List Connection

/-- A resolved reader-facing wire name for an already existing source. It
survives into emission metadata but adds no structural endpoint. -/
structure NamedWire where
  name : SourceName
  signalType : SignalType
  source : Source

structure Description where
  valid : Bool := true
  inputs : List Port := []
  outputs : List Connection := []
  children : List Child := []
  namedWires : List NamedWire := []

@[reducible] def portId (signals : SignalMap) (label : signals.Label) : PortId :=
  ⟨(signals.labels.ordinal label).val⟩

@[reducible] def childId (instances : InstancePorts) (child : instances.Name) : ChildId :=
  ⟨(instances.names.ordinal child).val⟩

def portList (signals : SignalMap) (names : SignalMapNaming signals) : List Port :=
  signals.labels.values.map fun label =>
    ⟨portId signals label, names.name label, signals.signalType label⟩

def sourceDescription {body : ModuleBody} :
    SignalSource body.ports body.instancePorts signalType → Source
  | .moduleInput port => .input (portId body.ports.inputs port)
  | .instanceOutput child port => .child (childId body.instancePorts child)
      (portId (body.instancePorts.ports child).outputs port)

/-- Extract every boundary port, child, and driven sink from a composite's
naming witness. -/
@[reducible] def ofCompositeNaming {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    (ports : ModulePortsNaming body.ports)
    (instanceName : body.instancePorts.Name → SourceName)
    (childNaming : (child : body.instancePorts.Name) →
      ModuleNaming (children child))
    (namedWires : List (Naming.NamedWire body) := []) : Description :=
  let source := fun {signalType} => sourceDescription (body := body) (signalType := signalType)
  { inputs := portList body.ports.inputs ports.inputs
    outputs := body.ports.outputs.labels.values.map fun port =>
      ⟨⟨portId body.ports.outputs port, ports.outputs.name port,
          body.ports.outputs.signalType port⟩,
        source (body.wiring.moduleOutput port)⟩
    children := body.instancePorts.names.values.map fun child =>
      { id := childId body.instancePorts child
        name := instanceName child
        module := ⟨body.instancePorts.ports child, children child, childNaming child⟩
        inputs := (body.instancePorts.ports child).inputs.labels.values.map fun port =>
          ⟨⟨portId (body.instancePorts.ports child).inputs port,
              (childNaming child).ports.inputs.name port,
              (body.instancePorts.ports child).inputs.signalType port⟩,
            source (body.wiring.instanceInput child port)⟩ }
    namedWires := namedWires.map fun wire =>
      { name := wire.name
        signalType := wire.signalType
        source := source wire.source } }

/-- Extract a description from a composite naming. Primitive and adapter
namings do not contain a child hierarchy and therefore return `none`. -/
def ofNaming {modulePorts : ModulePorts} {moduleStructure : ModuleStructure modulePorts} :
    ModuleNaming moduleStructure → Option Description
  | .composite _ ports instanceName childNaming namedWires =>
      some (ofCompositeNaming ports instanceName childNaming namedWires)
  | _ => none

@[simp] theorem ofNaming_composite {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    (key : ModuleKey) (ports : ModulePortsNaming body.ports)
    (instanceName : body.instancePorts.Name → SourceName)
    (childNaming : (child : body.instancePorts.Name) →
      ModuleNaming (children child))
    (namedWires : List (Naming.NamedWire body)) :
    ofNaming (ModuleNaming.composite key ports instanceName childNaming namedWires) =
      some (ofCompositeNaming ports instanceName childNaming namedWires) := rfl

/-- A successfully constructed description. This distinguishes the convenience
`build` failure sentinel without assigning semantic significance to names. -/
def Description.Valid (description : Description) : Prop :=
  description.valid = true

/-- The per-module certificate checks the translation, not hardware behavior. -/
structure Corresponds {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    (description : Description) (naming : ModuleNaming (.composite body children)) : Prop where
  same : some description = ofNaming naming

theorem ofNaming_some_valid {modulePorts : ModulePorts}
    {moduleStructure : ModuleStructure modulePorts}
    (naming : ModuleNaming moduleStructure) {description : Description}
    (same : ofNaming naming = some description) : description.Valid := by
  cases naming <;> simp [ofNaming] at same
  rw [← same]
  rfl

theorem Corresponds.valid {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    {description : Description}
    {naming : ModuleNaming (.composite body children)}
    (certificate : Corresponds description naming) : description.Valid := by
  exact ofNaming_some_valid naming certificate.same.symm

/-! ## Draft construction

`Description` remains the resolved, checked-translation boundary used by the
soundness development above. The builder works in a separate draft language so
authors may declare a typed wire before its driver is available. Finalization
resolves every wire to an ordinary structural source and retains the wire name
as emission metadata; neither `Description` nor structural semantics has an
unresolved-wire case. -/

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
  id : ChildId
  name : SourceName
  module : NamedModule
  inputs : List DraftConnection

structure DraftNamedWire where
  name : SourceName
  signalType : SignalType
  driver : Net signalType

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
  /-- Counts indexed instance stems without repeatedly traversing the much
  larger child records. This is builder bookkeeping and is discarded by
  finalization. -/
  indexedInstanceCounts : List (String × Nat) := []
  namedWires : List DraftNamedWire := []
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
  | .ok inputs => .ok
      { id := child.id, name := child.name, module := child.module, inputs := inputs }

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

@[simp] def finalizeNamedWire (wires : List WireDraft)
    (wire : DraftNamedWire) : Except BuildError NamedWire :=
  match resolveNet wires (wires.length + 1) wire.driver with
  | .ok source => .ok ⟨wire.name, wire.signalType, source⟩
  | .error error => .error error

@[simp] def finalizeNamedWires (wires : List WireDraft) :
    List DraftNamedWire → Except BuildError (List NamedWire)
  | [] => .ok []
  | wire :: rest => do
      let resolved ← finalizeNamedWire wires wire
      let resolvedRest ← finalizeNamedWires wires rest
      pure (resolved :: resolvedRest)

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
                | .ok children =>
                    if _uniqueNamedWires :
                        (draft.namedWires.map (fun wire => wire.name)).Nodup then
                      match finalizeNamedWires draft.wires draft.namedWires with
                      | .error error => .error error
                      | .ok namedWires => .ok
                          { inputs := draft.inputs, outputs := outputs,
                            children := children, namedWires := namedWires }
                    else
                      .error .duplicateWireName
      else
        .error .duplicateWireName

/-- Sentinel returned by the convenience `build` projection on failure. Its
explicit invalid status prevents it from matching any extracted production
description. -/
def invalidDescription : Description :=
  { valid := false }

theorem invalidDescription_not_valid : invalidDescription.valid = false := rfl

theorem invalidDescription_not_corresponds {body : ModuleBody}
    {children : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child)}
    (naming : ModuleNaming (.composite body children)) :
    ¬ Corresponds invalidDescription naming := by
  intro certificate
  have valid := certificate.valid
  simp [Description.Valid, invalidDescription] at valid

end Internal

/-- Run and validate an authoring construction without discarding diagnostics. -/
def buildResult (action : Builder Unit) : Except BuildError Description :=
  Internal.finalizeDraft (action {}).2

/-- Finalize a construction. On failure this returns an explicitly invalid
sentinel which cannot correspond to an extracted production description; use
`buildResult` directly when diagnostics are needed. -/
def build (action : Builder Unit) : Description :=
  match buildResult action with
  | .ok description => description
  | .error _ => Internal.invalidDescription

def input (name : SourceName) (signalType : SignalType) : Builder (Net signalType) :=
  fun state =>
    let id : PortId := ⟨state.inputs.length⟩
    (⟨.source (.input id)⟩,
      { state with inputs := state.inputs ++ [⟨id, name, signalType⟩] })

def output (name : SourceName) (net : Net signalType) : Builder Unit :=
  fun state =>
    let id : PortId := ⟨state.outputs.length⟩
    ((), { state with outputs := state.outputs ++
      [{ port := ⟨id, name, signalType⟩, driver := net }] })

/-- A construction tied to one typed module boundary.  The boundary naming is
supplied once when the construction is built.  Existing unbound `Builder`
actions lift automatically, so placement, wires, registers, and logic retain
their ordinary APIs. -/
structure ModuleBuilder (ports : ModulePorts) (α : Type) : Type 1 where
  run : ModulePortsNaming ports → Builder α

namespace ModuleBuilder

instance : Monad (ModuleBuilder ports) where
  pure value := ⟨fun _ => pure value⟩
  bind action next := ⟨fun naming => do
    let value ← action.run naming
    (next value).run naming⟩

/-- Use an ordinary boundary-independent builder action inside a module
construction. -/
instance : Coe (Builder α) (ModuleBuilder ports α) where
  coe action := ⟨fun _ => action⟩

/-- Lift an ordinary boundary-independent builder action through `do`
notation inside a typed module construction. -/
instance : MonadLift Builder (ModuleBuilder ports) where
  monadLift action := ⟨fun _ => action⟩

@[circuit_description]
theorem bind_run (action : ModuleBuilder ports α)
    (next : α → ModuleBuilder ports β) (naming : ModulePortsNaming ports) :
    ((action >>= next).run naming) =
      (action.run naming >>= fun value => (next value).run naming) := rfl

@[circuit_description]
theorem pure_run (value : α)
    (naming : ModulePortsNaming ports) :
    ((pure value : ModuleBuilder ports α).run naming) =
      (pure value : Builder α) := rfl

@[circuit_description]
theorem lift_run (action : Builder α)
    (naming : ModulePortsNaming ports) :
    ((liftM action : ModuleBuilder ports α).run naming) = action := rfl

/-- Refer to one declared boundary input.  Merely referring to an input does
not declare it: `buildResult` obtains the complete canonical input list from
the module boundary. -/
def input (port : ports.inputs.Label) :
    ModuleBuilder ports (Net (ports.inputs.signalType port)) :=
  ⟨fun _ => pure ⟨.source (.input (portId ports.inputs port))⟩⟩

/-- Drive one declared boundary output with a net of its required type. -/
def output (port : ports.outputs.Label)
    (net : Net (ports.outputs.signalType port)) : ModuleBuilder ports Unit :=
  ⟨fun naming state =>
    ((), { state with outputs := state.outputs ++
      [{ port := ⟨portId ports.outputs port, naming.outputs.name port,
          ports.outputs.signalType port⟩, driver := net }] })⟩

/-- Run and validate a typed module construction without discarding build
diagnostics.  Every declared input is emitted once in canonical boundary
order, independently of how often the construction refers to it. -/
def buildResult (naming : ModulePortsNaming ports)
    (action : ModuleBuilder ports Unit) : Except BuildError Description :=
  Internal.finalizeDraft
    ((action.run naming) { inputs := portList ports.inputs naming.inputs }).2

/-- Finalize a typed module construction.  On failure, return the same invalid
sentinel used by the low-level builder projection. -/
def build (naming : ModulePortsNaming ports)
    (action : ModuleBuilder ports Unit) : Description :=
  match buildResult naming action with
  | .ok description => description
  | .error _ => Internal.invalidDescription

end ModuleBuilder

/-- Run an ordinary net-producing action and retain a name for its resolved
structural source. The returned net is unchanged, so naming has no semantic
effect and composes like a `let` binding. -/
def namedWire (name : SourceName) (action : Builder (Net signalType)) :
    Builder (Net signalType) :=
  fun state =>
    let (net, state) := action state
    (net, { state with namedWires := state.namedWires ++
      [{ name := name, signalType := signalType, driver := net }] })

/-- Declare a typed authoring wire whose driver may be assigned later. -/
def wire (name : SourceName) (signalType : SignalType) : Builder (Net signalType) :=
  fun state =>
    let id := state.nextWire
    let net : Net signalType := ⟨.wire id⟩
    (net,
      { state with
        wires := state.wires ++
          [{ id := id, name := name, signalType := signalType, drivers := [] }]
        namedWires := state.namedWires ++
          [{ name := name, signalType := signalType, driver := net }]
        nextWire := id + 1 })

/-- Bind and immediately drive a wire while preserving the binder's spelling
as emission metadata. -/
syntax "wire " ident " ← " term : doElem

/-- Bind and immediately drive a wire while checking an explicit signal type. -/
syntax "wire " ident " : " term " ← " term : doElem

/-- Declare a typed wire for a driver supplied later with `assign`. -/
syntax "wire " ident " : " term : doElem

macro_rules
  | `(doElem| wire $name:ident ← $action:term) => do
      let emittedName := Lean.Syntax.mkStrLit name.getId.toString
      `(doElem| let $name ←
          Silean.Authoring.CircuitDescription.namedWire $emittedName $action)
  | `(doElem| wire $name:ident : $signalType:term ← $action:term) => do
      let emittedName := Lean.Syntax.mkStrLit name.getId.toString
      `(doElem| let $name ←
          (Silean.Authoring.CircuitDescription.namedWire
            (signalType := $signalType) $emittedName $action))
  | `(doElem| wire $name:ident : $signalType:term) => do
      let emittedName := Lean.Syntax.mkStrLit name.getId.toString
      `(doElem| let $name ←
          Silean.Authoring.CircuitDescription.wire $emittedName $signalType)

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

private def indexedInstanceCount (stem : String) : List (String × Nat) → Nat
  | [] => 0
  | (other, count) :: rest =>
      if other = stem then count else indexedInstanceCount stem rest

private def incrementIndexedInstanceCount (stem : String) :
    List (String × Nat) → List (String × Nat)
  | [] => [(stem, 1)]
  | (other, count) :: rest =>
      if other = stem then (other, count + 1) :: rest
      else (other, count) :: incrementIndexedInstanceCount stem rest

@[simp] private theorem indexedInstanceCount_nil (stem : String) :
    indexedInstanceCount stem [] = 0 := rfl

@[simp] private theorem indexedInstanceCount_increment_same
    (stem : String) (counts : List (String × Nat)) :
    indexedInstanceCount stem (incrementIndexedInstanceCount stem counts) =
      indexedInstanceCount stem counts + 1 := by
  induction counts with
  | nil => simp [incrementIndexedInstanceCount, indexedInstanceCount]
  | cons entry rest induction =>
      rcases entry with ⟨other, count⟩
      by_cases same : other = stem
      · subst other
        simp [incrementIndexedInstanceCount, indexedInstanceCount]
      · simp [incrementIndexedInstanceCount, indexedInstanceCount, same, induction]

@[simp] private theorem indexedInstanceCount_increment_other
    {stem other : String} (different : other ≠ stem)
    (counts : List (String × Nat)) :
    indexedInstanceCount other (incrementIndexedInstanceCount stem counts) =
      indexedInstanceCount other counts := by
  have reverse : stem ≠ other := Ne.symm different
  induction counts with
  | nil => simp [incrementIndexedInstanceCount, indexedInstanceCount, reverse]
  | cons entry rest induction =>
      rcases entry with ⟨existing, count⟩
      by_cases same : existing = stem
      · subst existing
        simp [incrementIndexedInstanceCount, indexedInstanceCount, reverse]
      · by_cases queried : existing = other
        · subst existing
          simp [incrementIndexedInstanceCount, indexedInstanceCount, same]
        · simp [incrementIndexedInstanceCount, indexedInstanceCount, same,
            queried, induction]

/-- Place an existing production child under an explicit instance name,
preserving its full identity. -/
def placeNamed (name : SourceName) (module : NamedModule)
    (inputs : (port : module.ports.inputs.Label) → Net (module.ports.inputs.signalType port)) :
    Builder ((port : module.ports.outputs.Label) → Net (module.ports.outputs.signalType port)) :=
  fun state =>
    let id : ChildId := ⟨state.children.length⟩
    let indexedInstanceCounts :=
      match name with
      | .indexed stem _ =>
          incrementIndexedInstanceCount stem state.indexedInstanceCounts
      | _ => state.indexedInstanceCounts
    (fun port => ⟨.source (.child id (portId module.ports.outputs port))⟩,
      { state with
        children := state.children ++
          [{ id := id
             name := name
             module := module
             inputs := module.ports.inputs.labels.values.map fun port =>
               { port := ⟨portId module.ports.inputs port,
                   module.naming.ports.inputs.name port,
                   module.ports.inputs.signalType port⟩
                 driver := inputs port } }]
        indexedInstanceCounts := indexedInstanceCounts })

/-- Place an existing production child using a conventional stem and its
occurrence number as a deterministic instance name. Module-specific helpers
supply the stem, so their callers do not manually name each instance. An
indexed name with stem `mask`, for example, emits as `mask_0`. -/
def placeIndexed (stem : String) (module : NamedModule)
    (inputs : (port : module.ports.inputs.Label) → Net (module.ports.inputs.signalType port)) :
    Builder ((port : module.ports.outputs.Label) → Net (module.ports.outputs.signalType port)) :=
  fun state =>
    placeNamed (.indexed stem (indexedInstanceCount stem state.indexedInstanceCounts))
      module inputs state

attribute [circuit_description]
  bind_apply pure_apply build buildResult input output namedWire
  ModuleBuilder.run ModuleBuilder.input ModuleBuilder.output
  ModuleBuilder.build ModuleBuilder.buildResult
  Silean.Authoring.CircuitDescription.wire assign
  placeNamed placeIndexed
  Internal.findWire? Internal.replaceWire Internal.validateWireDrivers
  Internal.resolveNet Internal.validateWireSources Internal.finalizeConnection
  Internal.finalizeConnections Internal.finalizeChild Internal.finalizeChildren
  Internal.finalizeNamedWire Internal.finalizeNamedWires Internal.finalizeDraft

end Silean.Authoring.CircuitDescription
