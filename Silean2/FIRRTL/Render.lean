import Silean2.FIRRTL.Traversal

namespace Silean2.FIRRTL

open Silean2

abbrev RenderResult := Except String

def SourceName.render : SourceName → String
  | .plain value => value
  | .indexed stem index => s!"{stem}_{index}"
  | .scoped scope name => s!"{scope}_{name.render}"

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
        s!"{name.render} : {renderSignalType head headNaming}"
    | .cons head (.cons next tail),
        .cons name headNaming (.cons nextName nextNaming tailNaming) =>
        s!"{name.render} : {renderSignalType head headNaming}, " ++
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

def ModuleParameter.render : ModuleParameter → String
  | .natural value => toString value
  | .shape signalType => renderSignalTypeKey signalType

def ModuleKey.render (key : ModuleKey) : String :=
  String.intercalate "_"
    ([key.family, key.variant].filter (fun part => !part.isEmpty) ++
      key.specialization.map ModuleParameter.render)

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
  let rendered := names.map SourceName.render
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
      s!"input {(naming.inputs.name label).render} : {renderSignalType (ports.inputs.signalType label) (naming.inputTypes label)}") ++
    (ports.outputs.labels.values.map fun label =>
      s!"output {(naming.outputs.name label).render} : {renderSignalType (ports.outputs.signalType label) (naming.outputTypes label)}")

private def primitiveStatements {primitive : Primitive}
    (ports : ModulePortsNaming primitive.ports)
    (state : SignalMapNaming primitive.localState) :
    PrimitiveOperation primitive → List String
  | .not =>
      [s!"connect {(ports.outputs.name .output).render}, not({(ports.inputs.name .input).render})"]
  | .and =>
      [s!"connect {(ports.outputs.name .output).render}, and({(ports.inputs.name .left).render}, {(ports.inputs.name .right).render})"]
  | .or =>
      [s!"connect {(ports.outputs.name .output).render}, or({(ports.inputs.name .left).render}, {(ports.inputs.name .right).render})"]
  | .eq =>
      [s!"connect {(ports.outputs.name .output).render}, eq({(ports.inputs.name .left).render}, {(ports.inputs.name .right).render})"]
  | .register =>
      let stored := (state.name .stored).render
      [s!"reg {stored} : UInt<1>, clock",
       s!"connect {(ports.outputs.name .output).render}, {stored}",
       s!"connect {stored}, {(ports.inputs.name .input).render}"]

private def splitterStatements (splitter : SignalSplitter)
    (ports : ModulePortsNaming splitter.ports) : List String := match splitter with
  | .vector length element =>
      let aggregate := (ports.inputs.name AggregatePort.value).render
      (SignalSplitter.vector length element).ports.outputs.labels.values.zipIdx.map
        fun (label, index) =>
          s!"connect {(ports.outputs.name label).render}, {aggregate}[{index}]"
  | .tuple fields =>
      let aggregate := (ports.inputs.name AggregatePort.value).render
      let fieldNaming := match ports.inputTypes AggregatePort.value with
        | .tuple fieldNaming => fieldNaming
      (SignalSplitter.tuple fields).ports.outputs.labels.values.map fun label =>
        s!"connect {(ports.outputs.name label).render}, {aggregate}.{(fieldNaming.nameAt label).render}"

private def combinerStatements (combiner : SignalCombiner)
    (ports : ModulePortsNaming combiner.ports) : List String := match combiner with
  | .vector length element =>
      let aggregate := (ports.outputs.name AggregatePort.value).render
      (SignalCombiner.vector length element).ports.inputs.labels.values.zipIdx.map
        fun (label, index) =>
          s!"connect {aggregate}[{index}], {(ports.inputs.name label).render}"
  | .tuple fields =>
      let aggregate := (ports.outputs.name AggregatePort.value).render
      let fieldNaming := match ports.outputTypes AggregatePort.value with
        | .tuple fieldNaming => fieldNaming
      (SignalCombiner.tuple fields).ports.inputs.labels.values.map fun label =>
        s!"connect {aggregate}.{(fieldNaming.nameAt label).render}, {(ports.inputs.name label).render}"

private def sourceReference {body : ModuleBody}
    {children : (name : body.context.instances.Name) →
      ModuleStructure (body.context.instances.ports name)}
    (ports : ModulePortsNaming body.context.ports)
    (instanceName : body.context.instances.Name → SourceName)
    (childNaming : (name : body.context.instances.Name) →
      ModuleNaming (children name)) :
    SignalSource body.context.ports body.context.instances signalType → String
  | .moduleInput port => (ports.inputs.name port).render
  | .instanceOutput child port =>
      s!"{(instanceName child).render}.{((childNaming child).ports.outputs.name port).render}"

private def sinkReference {body : ModuleBody}
    {children : (name : body.context.instances.Name) →
      ModuleStructure (body.context.instances.ports name)}
    (ports : ModulePortsNaming body.context.ports)
    (instanceName : body.context.instances.Name → SourceName)
    (childNaming : (name : body.context.instances.Name) →
      ModuleNaming (children name)) :
    SignalSink body.context.ports body.context.instances signalType → String
  | .moduleOutput port => (ports.outputs.name port).render
  | .instanceInput child port =>
      s!"{(instanceName child).render}.{((childNaming child).ports.inputs.name port).render}"

private def compositeStatements {body : ModuleBody}
    {children : (name : body.context.instances.Name) →
      ModuleStructure (body.context.instances.ports name)}
    (ports : ModulePortsNaming body.context.ports)
    (instanceName : body.context.instances.Name → SourceName)
    (childNaming : (name : body.context.instances.Name) →
      ModuleNaming (children name)) : List String :=
  let instances := body.context.instances.names.values.flatMap fun child =>
    [s!"inst {(instanceName child).render} of {(childNaming child).key.render}",
     s!"connect {(instanceName child).render}.clock, clock"]
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
  pure s!"  {qualifier} {module.key.render} :\n{body}"

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
  let moduleNames := definitions.map (fun definition => definition.key.render)
  if let some invalid := moduleNames.find? (fun name => !isIdentifier name) then
    throw s!"invalid FIRRTL module identifier '{invalid}'"
  if let some duplicate := firstDuplicate? moduleNames then
    throw s!"duplicate FIRRTL module name '{duplicate}'"
  let occurrenceBodies ← (collectOccurrences naming).mapM fun occurrence => do
    let body ← renderModuleBody occurrence.definition.naming
    pure (occurrence.definition.key.render, body)
  validateDefinitionBodies [] occurrenceBodies
  let rendered ← definitions.mapM fun definition =>
    renderDefinition (definition.key == rootKey) definition
  pure s!"FIRRTL version 4.0.0\ncircuit {rootKey.render} :\n{String.intercalate "\n\n" rendered}\n"

end Silean2.FIRRTL
