import Silean.Authoring.ModuleInstances

namespace Silean.Authoring

/-! # Structural wiring authoring

`module_wiring` connects a previously declared module boundary and child
instance set. It generates the typed `Wiring`, the resulting `ModuleBody`, and
the composite `ModuleStructure`. Every parent output and child input receives
exactly one `SignalSource`; Lean's types ensure that each source has the signal
type required by its destination.

The declaration records simultaneous connections, not an evaluation order.
Dependency schedules used to prove existence and uniqueness are declared later
and do not change the wiring's meaning. `module_design` normally invokes this
lower-level command after `module_instances`.
-/

open Lean Elab Command
open Lean.Parser.Term

/-! ## Command syntax -/

declare_syntax_cat moduleWiringParam
syntax "(" ident " : " term ")" : moduleWiringParam

declare_syntax_cat moduleWireSource
syntax ident : moduleWireSource
syntax ident "[" term "]" : moduleWireSource
syntax ident "(" term,* ")" "[" term "]" : moduleWireSource
syntax "from" "(" term ")" : moduleWireSource

declare_syntax_cat moduleWireEntry
syntax term " := " moduleWireSource : moduleWireEntry

declare_syntax_cat moduleWireGroup
syntax ident " { " moduleWireEntry,* " }" : moduleWireGroup
syntax "instance" "(" term ")" " { " moduleWireEntry,* " }" : moduleWireGroup

/--
Declare all wiring at one structural layer, grouped first by parent outputs and
then by child instance. A source of the form `input.port` is a parent input;
`child.port` is a fixed child output, and `child(index)[.port]` is an indexed
child output. `from (source)` retains an ordinary typed `SignalSource`
expression when a connection is computed by a reusable Lean helper. The
command generates the conventional ordinary `wiring`,
`body`, and `moduleStructure` declarations used by the rest of Silean.
-/
syntax (name := moduleWiring)
  "module_wiring " ident moduleWiringParam* " for " term " where "
    moduleWireGroup* : command

/-! ## Elaboration -/

private structure ModuleParam where
  binder : TSyntax ``Lean.Parser.Term.bracketedBinder
  argument : TSyntax `term

private def parseParam (param : TSyntax `moduleWiringParam) :
    CommandElabM ModuleParam :=
  match param with
  | `(moduleWiringParam| ($name:ident : $type:term)) => do
      pure {
        binder := ← `(bracketedBinder| ($name : $type))
        argument := name
      }
  | _ => throwUnsupportedSyntax

private def elaborateSource (contextName : TSyntax `ident)
    (source : TSyntax `moduleWireSource) : CommandElabM (TSyntax `term) := do
  match source with
  | `(moduleWireSource| $qualified:ident) =>
      let qualifiedName := qualified.getId
      if qualifiedName.isAtomic then
        throwErrorAt qualified
          "expected a source such as `input.value` or `child.output`"
      let name := mkIdentFrom qualified qualifiedName.getPrefix
      let port := mkIdentFrom qualified (Name.mkSimple qualifiedName.getString!)
      if name.getId == `input then
        `(($contextName).moduleInput .$port)
      else
        `(($contextName).instanceOutput .$name .$port)
  | `(moduleWireSource| $name:ident [$port:term]) =>
      if name.getId == `input then
        `(($contextName).moduleInput $port)
      else
        `(($contextName).instanceOutput .$name $port)
  | `(moduleWireSource| $name:ident ($indices:term,*) [$port:term]) =>
      if name.getId == `input then
        throwErrorAt name "a parent input cannot have instance indices"
      else
        `(($contextName).instanceOutput (.$name $indices:term*) $port)
  | `(moduleWireSource| from ($source:term)) => pure source
  | _ => throwUnsupportedSyntax

private def outputAlternative (contextName : TSyntax `ident)
    (entry : TSyntax `moduleWireEntry) :
    CommandElabM (TSyntax ``Lean.Parser.Term.matchAlt) := do
  let `(moduleWireEntry| $sink:term := $source:moduleWireSource) := entry
    | throwUnsupportedSyntax
  let source ← elaborateSource contextName source
  `(matchAltExpr| | $sink => $source)

private def inputAlternative (contextName : TSyntax `ident)
    (instancePattern : TSyntax `term) (entry : TSyntax `moduleWireEntry) :
    CommandElabM (TSyntax ``Lean.Parser.Term.matchAlt) := do
  let `(moduleWireEntry| $sink:term := $source:moduleWireSource) := entry
    | throwUnsupportedSyntax
  let source ← elaborateSource contextName source
  `(matchAltExpr| | $instancePattern, $sink => $source)

elab_rules : command
  | `(module_wiring $wiringName:ident $params:moduleWiringParam*
        for $context:term where $groups:moduleWireGroup*) => do
    let parsedParams ← params.mapM parseParam
    let binders := parsedParams.map (·.binder)
    let arguments := parsedParams.map (·.argument)
    let contextName := mkIdentFrom wiringName `c
    let mut outputAlternatives : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut inputAlternatives : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut sawOutputs := false
    for group in groups do
      match group with
      | `(moduleWireGroup| $kind:ident { $entries:moduleWireEntry,* }) =>
          unless kind.getId == `outputs do
            throwErrorAt kind "expected an `outputs` wiring group"
          if sawOutputs then throwErrorAt group "duplicate `outputs` wiring group"
          sawOutputs := true
          outputAlternatives ← entries.getElems.mapM
            (outputAlternative contextName)
      | `(moduleWireGroup| instance ($instancePattern:term) {
          $entries:moduleWireEntry,* }) =>
          inputAlternatives := inputAlternatives ++
            (← entries.getElems.mapM
              (inputAlternative contextName instancePattern))
      | _ => throwUnsupportedSyntax
    unless sawOutputs do
      throwErrorAt wiringName "module_wiring requires an `outputs` group"

    let bodyName := mkIdentFrom wiringName `body
    let moduleStructureName := mkIdentFrom wiringName `moduleStructure
    let structuralChildrenName := mkIdentFrom wiringName `structuralChildren

    elabCommand <| ← `(
      def $wiringName $binders:bracketedBinder* :
          Silean.Wiring ($context).ports ($context).instancePorts :=
        let $contextName := $context
        {
          moduleOutput := fun $outputAlternatives:matchAlt*
          instanceInput := fun $inputAlternatives:matchAlt*
        }
    )
    elabCommand <| ← `(
      @[reducible] def $bodyName $binders:bracketedBinder* :
          Silean.ModuleBody :=
        ⟨$context, $wiringName $arguments:term*⟩
    )
    elabCommand <| ← `(
      def $moduleStructureName $binders:bracketedBinder* :
          Silean.ModuleStructure ($context).ports :=
        .composite ($bodyName $arguments:term*)
          ($structuralChildrenName $arguments:term*)
    )

end Silean.Authoring
