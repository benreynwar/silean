import Silean.Naming.ModuleNaming

namespace Silean.FIRRTL

open Silean Silean.Naming

inductive PortOccurrence (ports : ModulePorts) where
  | input (label : ports.inputs.Label)
  | output (label : ports.outputs.Label)

def PortOccurrence.signalType : PortOccurrence ports → SignalType
  | .input label => ports.inputs.signalType label
  | .output label => ports.outputs.signalType label

def PortOccurrence.name (naming : ModulePortsNaming ports) :
    PortOccurrence ports → SourceName
  | .input label => naming.inputs.name label
  | .output label => naming.outputs.name label

def portOccurrences (ports : ModulePorts) : List (PortOccurrence ports) :=
  ports.inputs.labels.values.map .input ++
    ports.outputs.labels.values.map .output

structure ConnectionOccurrence (body : ModuleBody) where
  signalType : SignalType
  sink : SignalSink body.ports body.instancePorts signalType
  driver : SignalSource body.ports body.instancePorts signalType

def connectionOccurrences (body : ModuleBody) : List (ConnectionOccurrence body) :=
  body.ports.outputs.labels.values.map (fun output =>
      { signalType := body.ports.outputs.signalType output
        sink := .moduleOutput output
        driver := body.wiring.moduleOutput output }) ++
    body.instancePorts.names.values.flatMap (fun child =>
      (body.instancePorts.ports child).inputs.labels.values.map (fun input =>
        { signalType :=
            (body.instancePorts.ports child).inputs.signalType input
          sink := .instanceInput child input
          driver := body.wiring.instanceInput child input }))

structure InstanceOccurrence where
  sourceName : SourceName
  targetKey : ModuleKey

def instanceOccurrences :
    (naming : ModuleNaming moduleStructure) → List InstanceOccurrence
  | .primitive .. | .blackbox .. | .splitter .. | .combiner .. => []
  | @ModuleNaming.composite body _ _ _ instanceName childNaming =>
      body.instancePorts.names.values.map fun name =>
        ⟨instanceName name, (childNaming name).key⟩

structure ModuleOccurrence where
  path : List SourceName
  definition : NamedModule

private def collectOccurrencesAt (path : List SourceName) :
    (naming : ModuleNaming moduleStructure) → List ModuleOccurrence
  | .primitive key ports state operation =>
      [⟨path, ⟨_, _, .primitive key ports state operation⟩⟩]
  | .blackbox key ports state =>
      [⟨path, ⟨_, _, .blackbox key ports state⟩⟩]
  | .splitter splitter key ports =>
      [⟨path, ⟨_, _, .splitter splitter key ports⟩⟩]
  | .combiner combiner key ports =>
      [⟨path, ⟨_, _, .combiner combiner key ports⟩⟩]
  | @ModuleNaming.composite body children key ports instanceName childNaming =>
      ⟨path, ⟨_, _, .composite key ports instanceName childNaming⟩⟩ ::
        body.instancePorts.names.values.flatMap (fun child =>
          collectOccurrencesAt (path ++ [instanceName child]) (childNaming child))

def collectOccurrences (naming : ModuleNaming moduleStructure) : List ModuleOccurrence :=
  collectOccurrencesAt [] naming

private def insertDefinition (definitions : List NamedModule)
    (definition : NamedModule) : List NamedModule :=
  if definitions.any fun present => present.key == definition.key then
    definitions
  else
    definitions ++ [definition]

/-! Definitions are collected child-first and shared by `ModuleKey`. The later
renderer remains responsible for diagnosing two differently rendered bodies
that were assigned the same key. -/
private def collectDefinitionsInto (definitions : List NamedModule) :
    (naming : ModuleNaming moduleStructure) → List NamedModule
  | .primitive key ports state operation =>
      insertDefinition definitions ⟨_, _, .primitive key ports state operation⟩
  | .blackbox key ports state =>
      insertDefinition definitions ⟨_, _, .blackbox key ports state⟩
  | .splitter splitter key ports =>
      insertDefinition definitions ⟨_, _, .splitter splitter key ports⟩
  | .combiner combiner key ports =>
      insertDefinition definitions ⟨_, _, .combiner combiner key ports⟩
  | @ModuleNaming.composite body children key ports instanceName childNaming =>
      let withChildren := body.instancePorts.names.values.foldl
        (fun collected child => collectDefinitionsInto collected (childNaming child))
        definitions
      insertDefinition withChildren
        ⟨_, _, .composite key ports instanceName childNaming⟩

def collectDefinitions (naming : ModuleNaming moduleStructure) : List NamedModule :=
  collectDefinitionsInto [] naming

def definitionKeys (naming : ModuleNaming moduleStructure) : List ModuleKey :=
  (collectDefinitions naming).map (fun definition => definition.key)

end Silean.FIRRTL
