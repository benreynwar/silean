import Silean2.FIRRTL.Traversal

namespace Silean2.FIRRTL

open Silean2 Silean2.Naming

abbrev RenderResult := Except String

def renderSourceName : SourceName → String
  | .plain value => value
  | .indexed stem index => s!"{stem}_{index}"
  | .scoped scope name => s!"{scope}_{renderSourceName name}"

mutual
  def renderSignalType : (signalType : SignalType) →
      SignalTypeNaming signalType → String
    | .bit, .bit => "UInt<1>"
    | .vector length element, .vector elementNaming =>
        s!"{renderSignalType element elementNaming}[{length}]"
    | .tuple fields, .tuple fieldNaming =>
        "{ " ++ renderSignalTypes fields fieldNaming ++ " }"

  def renderSignalTypes : (signalTypes : SignalTypes) →
      SignalTypesNaming signalTypes → String
    | .nil, .nil => ""
    | .cons head .nil, .cons name headNaming .nil =>
        s!"{renderSourceName name} : {renderSignalType head headNaming}"
    | .cons head (.cons next tail),
        .cons name headNaming (.cons nextName nextNaming tailNaming) =>
        s!"{renderSourceName name} : {renderSignalType head headNaming}, " ++
          renderSignalTypes (.cons next tail)
            (.cons nextName nextNaming tailNaming)
end

def renderSignalTypeKey : SignalType → String
  | .bit => "bit"
  | .vector length element => s!"v{length}_{renderSignalTypeKey element}"
  | .tuple fields => s!"t_{renderSignalTypesKey fields}"
where
  renderSignalTypesKey : SignalTypes → String
    | .nil => "unit"
    | .cons head tail => s!"{renderSignalTypeKey head}_{renderSignalTypesKey tail}"

def renderModuleParameter : ModuleParameter → String
  | .natural value => toString value
  | .shape signalType => renderSignalTypeKey signalType

def renderModuleKey (key : ModuleKey) : String :=
  String.intercalate "_"
    ([key.family, key.variant].filter (fun part => !part.isEmpty) ++
      key.specialization.map renderModuleParameter)

private def firstDuplicate? [BEq α] : List α → Option α
  | [] => none
  | head :: tail => if tail.contains head then some head else firstDuplicate? tail

private def isIdentifier (value : String) : Bool :=
  match value.toList with
  | [] => false
  | head :: tail =>
      (head.isAlpha || head == '_') &&
        tail.all (fun character => character.isAlphanum || character == '_')

private def validateLocalNames (names : List SourceName) : RenderResult Unit :=
  let rendered := names.map renderSourceName
  if let some invalid := rendered.find? (fun name => !isIdentifier name) then
    throw s!"invalid FIRRTL identifier '{invalid}'"
  else match firstDuplicate? rendered with
    | some duplicate => throw s!"duplicate FIRRTL component name '{duplicate}'"
    | none =>
        if rendered.contains "clock" then
          throw "the FIRRTL component name 'clock' is reserved for the structural clock"
        else pure ()

private def indentLines (lines : List String) : String :=
  String.intercalate "\n" (lines.map ("    " ++ ·))

private def renderPorts (naming : ModulePortsNaming ports) : List String :=
  "input clock : Clock" ::
    (ports.inputs.labels.values.map fun label =>
      s!"input {renderSourceName (naming.inputs.name label)} : {renderSignalType (ports.inputs.signalType label) (naming.inputTypes label)}") ++
    (ports.outputs.labels.values.map fun label =>
      s!"output {renderSourceName (naming.outputs.name label)} : {renderSignalType (ports.outputs.signalType label) (naming.outputTypes label)}")

private def primitiveStatements {primitive : Primitive}
    (ports : ModulePortsNaming primitive.ports)
    (state : SignalMapNaming primitive.localState) :
    PrimitiveOperation primitive → List String
  | .not =>
      [s!"connect {renderSourceName (ports.outputs.name .output)}, not({renderSourceName (ports.inputs.name .input)})"]
  | .and =>
      [s!"connect {renderSourceName (ports.outputs.name .output)}, and({renderSourceName (ports.inputs.name .left)}, {renderSourceName (ports.inputs.name .right)})"]
  | .or =>
      [s!"connect {renderSourceName (ports.outputs.name .output)}, or({renderSourceName (ports.inputs.name .left)}, {renderSourceName (ports.inputs.name .right)})"]
  | .eq =>
      [s!"connect {renderSourceName (ports.outputs.name .output)}, eq({renderSourceName (ports.inputs.name .left)}, {renderSourceName (ports.inputs.name .right)})"]
  | .register =>
      let stored := renderSourceName (state.name .stored)
      [s!"reg {stored} : UInt<1>, clock",
       s!"connect {renderSourceName (ports.outputs.name .output)}, {stored}",
       s!"connect {stored}, {renderSourceName (ports.inputs.name .input)}"]

private def splitterStatements (splitter : SignalSplitter)
    (ports : ModulePortsNaming splitter.ports) : List String := match splitter with
  | .vector length element =>
      let aggregate := renderSourceName (ports.inputs.name AggregatePort.value)
      (SignalSplitter.vector length element).ports.outputs.labels.values.zipIdx.map
        fun (label, index) =>
          s!"connect {renderSourceName (ports.outputs.name label)}, {aggregate}[{index}]"
  | .tuple fields =>
      let aggregate := renderSourceName (ports.inputs.name AggregatePort.value)
      let fieldNaming := match ports.inputTypes AggregatePort.value with
        | .tuple fieldNaming => fieldNaming
      (SignalSplitter.tuple fields).ports.outputs.labels.values.map fun label =>
        s!"connect {renderSourceName (ports.outputs.name label)}, {aggregate}.{renderSourceName (fieldNaming.nameAt label)}"

private def combinerStatements (combiner : SignalCombiner)
    (ports : ModulePortsNaming combiner.ports) : List String := match combiner with
  | .vector length element =>
      let aggregate := renderSourceName (ports.outputs.name AggregatePort.value)
      (SignalCombiner.vector length element).ports.inputs.labels.values.zipIdx.map
        fun (label, index) =>
          s!"connect {aggregate}[{index}], {renderSourceName (ports.inputs.name label)}"
  | .tuple fields =>
      let aggregate := renderSourceName (ports.outputs.name AggregatePort.value)
      let fieldNaming := match ports.outputTypes AggregatePort.value with
        | .tuple fieldNaming => fieldNaming
      (SignalCombiner.tuple fields).ports.inputs.labels.values.map fun label =>
        s!"connect {aggregate}.{renderSourceName (fieldNaming.nameAt label)}, {renderSourceName (ports.inputs.name label)}"

private def sourceReference {body : ModuleBody}
    {children : (name : body.context.instances.Name) →
      ModuleStructure (body.context.instances.ports name)}
    (ports : ModulePortsNaming body.context.ports)
    (instanceName : body.context.instances.Name → SourceName)
    (childNaming : (name : body.context.instances.Name) →
      ModuleNaming (children name)) :
    SignalSource body.context.ports body.context.instances signalType → String
  | .moduleInput port => renderSourceName (ports.inputs.name port)
  | .instanceOutput child port =>
      s!"{renderSourceName (instanceName child)}.{renderSourceName ((childNaming child).ports.outputs.name port)}"

private def sinkReference {body : ModuleBody}
    {children : (name : body.context.instances.Name) →
      ModuleStructure (body.context.instances.ports name)}
    (ports : ModulePortsNaming body.context.ports)
    (instanceName : body.context.instances.Name → SourceName)
    (childNaming : (name : body.context.instances.Name) →
      ModuleNaming (children name)) :
    SignalSink body.context.ports body.context.instances signalType → String
  | .moduleOutput port => renderSourceName (ports.outputs.name port)
  | .instanceInput child port =>
      s!"{renderSourceName (instanceName child)}.{renderSourceName ((childNaming child).ports.inputs.name port)}"

private def compositeStatements {body : ModuleBody}
    {children : (name : body.context.instances.Name) →
      ModuleStructure (body.context.instances.ports name)}
    (ports : ModulePortsNaming body.context.ports)
    (instanceName : body.context.instances.Name → SourceName)
    (childNaming : (name : body.context.instances.Name) →
      ModuleNaming (children name)) : List String :=
  let instances := body.context.instances.names.values.flatMap fun child =>
    [s!"inst {renderSourceName (instanceName child)} of {renderModuleKey (childNaming child).key}",
     s!"connect {renderSourceName (instanceName child)}.clock, clock"]
  let connections := (connectionOccurrences body).map fun connection =>
    s!"connect {sinkReference ports instanceName childNaming connection.sink}, {sourceReference ports instanceName childNaming connection.driver}"
  instances ++ connections

private def renderModuleBody :
    (naming : ModuleNaming moduleStructure) → RenderResult String
  | .primitive _ ports state operation => do
      validateLocalNames (ports.names ++ state.names)
      pure (indentLines (renderPorts ports ++ primitiveStatements ports state operation))
  | .splitter splitter _ ports => do
      validateLocalNames ports.names
      pure (indentLines (renderPorts ports ++ splitterStatements splitter ports))
  | .combiner combiner _ ports => do
      validateLocalNames ports.names
      pure (indentLines (renderPorts ports ++ combinerStatements combiner ports))
  | @ModuleNaming.composite body children _ ports instanceName childNaming => do
      validateLocalNames (ports.names ++ body.context.instances.names.values.map instanceName)
      pure (indentLines (renderPorts ports ++
        compositeStatements ports instanceName childNaming))

private def renderDefinition (isPublic : Bool) (module : NamedModule) : RenderResult String := do
  let body ← renderModuleBody module.naming
  let qualifier := if isPublic then "public module" else "module"
  pure s!"  {qualifier} {renderModuleKey module.key} :\n{body}"

private def validateDefinitionBodies :
    List (String × String) → List (String × String) → RenderResult Unit
  | _, [] => pure ()
  | seen, (name, body) :: rest =>
      match seen.find? (fun present => present.1 == name) with
      | some present =>
          if present.2 == body then validateDefinitionBodies seen rest
          else throw s!"module key '{name}' names two different FIRRTL definitions"
      | none => validateDefinitionBodies (seen ++ [(name, body)]) rest

def renderCircuit (naming : ModuleNaming moduleStructure) : RenderResult String := do
  let definitions := collectDefinitions naming
  let rootKey := naming.key
  let moduleNames := definitions.map (fun definition => renderModuleKey definition.key)
  if let some invalid := moduleNames.find? (fun name => !isIdentifier name) then
    throw s!"invalid FIRRTL module identifier '{invalid}'"
  if let some duplicate := firstDuplicate? moduleNames then
    throw s!"duplicate FIRRTL module name '{duplicate}'"
  let occurrenceBodies ← (collectOccurrences naming).mapM fun occurrence => do
    let body ← renderModuleBody occurrence.definition.naming
    pure (renderModuleKey occurrence.definition.key, body)
  validateDefinitionBodies [] occurrenceBodies
  let rendered ← definitions.mapM fun definition =>
    renderDefinition (definition.key == rootKey) definition
  pure s!"FIRRTL version 4.0.0\ncircuit {renderModuleKey rootKey} :\n{String.intercalate "\n\n" rendered}\n"

end Silean2.FIRRTL
