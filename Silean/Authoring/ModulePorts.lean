import Silean.Foundation.ModulePorts
import Silean.Foundation.DeriveEnumeration
import Silean.Naming.ModuleNaming
import Silean.Authoring.SignalSchema

namespace Silean.Authoring

open Lean Elab Command

declare_syntax_cat modulePortsParam
syntax "(" ident " : " term ")" : modulePortsParam

declare_syntax_cat modulePortsNamingParam
syntax "(" ident " : " term " := " term ")" : modulePortsNamingParam

declare_syntax_cat modulePortsNamingClause
syntax "with " modulePortsNamingParam,+ :
  modulePortsNamingClause

declare_syntax_cat modulePortEntry
declare_syntax_cat modulePortModifier
syntax "(" ident " := " term ")" : modulePortModifier
syntax ident ident modulePortModifier* " : " term : modulePortEntry

/--
Declare a module boundary once and generate its ordinary Lean labels, signal
maps, `ModulePorts`, and port-naming metadata.

Optional `with` binders support aggregate signal types whose emitted component
names are supplied by the caller. They generate `Naming.portsWithNaming` and
state the positional defaults used by the generated `Naming.ports`. A port's
`(schema := ...)` supplies those component names from a `SignalSchema` (a thin
authoring name for `SignalTypeNaming`). A direction with no entries is
represented by `NoSignal` and `emptySignalMap`.
-/
syntax (name := modulePorts)
  "module_ports " ident modulePortsParam* (modulePortsNamingClause)?
    " where " modulePortEntry,* : command

open Lean.Parser.Term

private structure PortDecl where
  label : TSyntax `ident
  sourceName : TSyntax `term
  signalType : TSyntax `term
  typeNaming : Option (TSyntax `term)

private def parsePortDecl (entry : TSyntax `modulePortEntry) :
    CommandElabM (Bool × PortDecl) := do
  let make (isInput : Bool) (label : TSyntax `ident)
      (emitted : Option (TSyntax `term)) (signalType : TSyntax `term)
      (typeNaming : Option (TSyntax `term)) := do
    let sourceName ← match emitted with
      | some value => `(($value : Silean.Naming.SourceName))
      | none =>
          let literal := Syntax.mkStrLit label.getId.toString
          `(($literal : Silean.Naming.SourceName))
    pure (isInput, { label, sourceName, signalType, typeNaming })
  match entry with
  | `(modulePortEntry| $direction:ident $label:ident
        $modifiers:modulePortModifier* : $signalType:term) =>
      let mut emitted : Option (TSyntax `term) := none
      let mut typeNaming : Option (TSyntax `term) := none
      for modifier in modifiers do
        let `(modulePortModifier| ($key:ident := $value:term)) := modifier
          | throwUnsupportedSyntax
        if key.getId == `name then
          if emitted.isSome then throwErrorAt key "duplicate `name` modifier"
          emitted := some value
        else if key.getId == `schema then
          if typeNaming.isSome then
            throwErrorAt key "duplicate component schema or naming"
          typeNaming := some value
        else
          throwErrorAt key "expected a `name` or `schema` port modifier"
      if direction.getId == `input then
        make true label emitted signalType typeNaming
      else if direction.getId == `output then
        make false label emitted signalType typeNaming
      else
        throwErrorAt direction "expected `input` or `output`"
  | _ => throwUnsupportedSyntax

private def parseParam (param : TSyntax `modulePortsParam) :
    CommandElabM (TSyntax ``Parser.Term.bracketedBinder × TSyntax `term) :=
  match param with
  | `(modulePortsParam| ($name:ident : $type:term)) => do
      pure (← `(bracketedBinder| ($name : $type)), name)
  | _ => throwUnsupportedSyntax

private def constructorSyntax (decl : PortDecl) : CommandElabM (TSyntax ``Parser.Command.ctor) :=
  `(Parser.Command.ctor| | $(decl.label):ident)

private def mapAlternative (decl : PortDecl) : CommandElabM (TSyntax ``Parser.Term.matchAlt) :=
  let label := decl.label
  `(matchAltExpr| | .$label => $(decl.signalType))

private def nameAlternative (decl : PortDecl) : CommandElabM (TSyntax ``Parser.Term.matchAlt) :=
  let label := decl.label
  `(matchAltExpr| | .$label => $(decl.sourceName))

private def typeNamingAlternative (decl : PortDecl) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) := do
  let chosenNaming ← decl.typeNaming.getDM do
    `(Silean.Naming.SignalTypeNaming.positional $(decl.signalType))
  let label := decl.label
  `(matchAltExpr| | .$label => $chosenNaming)

elab_rules : command
  | `(module_ports $portsName:ident $params:modulePortsParam*
        $[$namingClause:modulePortsNamingClause]? where $entries:modulePortEntry,*) => do
    let parsed ← entries.getElems.mapM parsePortDecl
    let inputs := parsed.filterMap fun (isInput, decl) => if isInput then some decl else none
    let outputs := parsed.filterMap fun (isInput, decl) => if isInput then none else some decl

    let parsedParams ← params.mapM parseParam
    let binders := parsedParams.map (·.1)
    let arguments := parsedParams.map (·.2)
    let inputIdent := mkIdentFrom portsName `Input
    let outputIdent := mkIdentFrom portsName `Output
    let inputMapIdent := mkIdentFrom portsName `inputMap
    let outputMapIdent := mkIdentFrom portsName `outputMap
    let namingPortsIdent := mkIdentFrom portsName `Naming.ports
    let namingWithIdent := mkIdentFrom portsName `Naming.portsWithNaming

    let inputNames : TSyntax `term ← if inputs.isEmpty then
      `(fun impossible => nomatch impossible)
    else
      let alternatives ← inputs.mapM nameAlternative
      `(fun $alternatives:matchAlt*)
    let outputNames : TSyntax `term ← if outputs.isEmpty then
      `(fun impossible => nomatch impossible)
    else
      let alternatives ← outputs.mapM nameAlternative
      `(fun $alternatives:matchAlt*)
    let inputTypeNames : TSyntax `term ← if inputs.isEmpty then
      `(fun impossible => nomatch impossible)
    else
      let alternatives ← inputs.mapM typeNamingAlternative
      `(fun $alternatives:matchAlt*)
    let outputTypeNames : TSyntax `term ← if outputs.isEmpty then
      `(fun impossible => nomatch impossible)
    else
      let alternatives ← outputs.mapM typeNamingAlternative
      `(fun $alternatives:matchAlt*)

    if inputs.isEmpty then
      elabCommand <| ← `(
        abbrev $inputIdent := Silean.NoSignal
      )
      elabCommand <| ← `(
        @[reducible] def $inputMapIdent $binders:bracketedBinder* : Silean.SignalMap :=
          Silean.emptySignalMap
      )
    else
      let constructors ← inputs.mapM constructorSyntax
      let alternatives ← inputs.mapM mapAlternative
      elabCommand <| ← `(
        inductive $inputIdent where
          $constructors:ctor*
        deriving Silean.Enumeration
      )
      elabCommand <| ← `(
        @[reducible] def $inputMapIdent $binders:bracketedBinder* : Silean.SignalMap :=
          Silean.EnumeratedMap.of $inputIdent fun $alternatives:matchAlt*
      )

    if outputs.isEmpty then
      elabCommand <| ← `(
        abbrev $outputIdent := Silean.NoSignal
      )
      elabCommand <| ← `(
        @[reducible] def $outputMapIdent $binders:bracketedBinder* : Silean.SignalMap :=
          Silean.emptySignalMap
      )
    else
      let constructors ← outputs.mapM constructorSyntax
      let alternatives ← outputs.mapM mapAlternative
      elabCommand <| ← `(
        inductive $outputIdent where
          $constructors:ctor*
        deriving Silean.Enumeration
      )
      elabCommand <| ← `(
        @[reducible] def $outputMapIdent $binders:bracketedBinder* : Silean.SignalMap :=
          Silean.EnumeratedMap.of $outputIdent fun $alternatives:matchAlt*
      )
    elabCommand <| ← `(
      @[reducible] def $portsName $binders:bracketedBinder* : Silean.ModulePorts :=
        ⟨$inputMapIdent $arguments:term*, $outputMapIdent $arguments:term*⟩
    )

    match namingClause with
    | none =>
        elabCommand <| ← `(
          def $namingPortsIdent $binders:bracketedBinder* : Silean.Naming.ModulePortsNaming
              ($portsName $arguments:term*) where
            inputs := ⟨$inputNames⟩
            outputs := ⟨$outputNames⟩
            inputTypes := $inputTypeNames
            outputTypes := $outputTypeNames
        )
    | some clause =>
        let `(modulePortsNamingClause| with $namingParams:modulePortsNamingParam,*) := clause
          | throwUnsupportedSyntax
        let parsedNamingParams ← namingParams.getElems.mapM fun parameter => do
          let `(modulePortsNamingParam|
              ($name:ident : $type:term := $defaultValue:term)) := parameter
            | throwUnsupportedSyntax
          let binder ← `(bracketedBinder| ($name : $type))
          pure (binder, defaultValue)
        let namingBinders := parsedNamingParams.map (·.1)
        let defaultNamings := parsedNamingParams.map (·.2)
        elabCommand <| ← `(
          def $namingWithIdent $binders:bracketedBinder* $namingBinders:bracketedBinder* :
              Silean.Naming.ModulePortsNaming ($portsName $arguments:term*) where
            inputs := ⟨$inputNames⟩
            outputs := ⟨$outputNames⟩
            inputTypes := $inputTypeNames
            outputTypes := $outputTypeNames
        )
        elabCommand <| ← `(
          def $namingPortsIdent $binders:bracketedBinder* :
              Silean.Naming.ModulePortsNaming ($portsName $arguments:term*) :=
            $namingWithIdent $arguments:term* $defaultNamings:term*
        )

end Silean.Authoring
