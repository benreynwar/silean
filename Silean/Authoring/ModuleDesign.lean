import Silean.Authoring.ModuleWiring

namespace Silean.Authoring

/-! # Composite module authoring

`module_design` is the main design-side command for composite hardware. A
single declaration combines a new or existing boundary, concrete child
modules, optional named internal wires, typed wiring, and recursive emission
naming. It expands through the
lower-level `module_ports`, `module_instances`, and `module_wiring` commands
and then packages the result as a `Naming.NamedModule`.

The generated `ModuleStructure` is deliberately independent of behavioral
contracts and certification proofs. Those are authored separately so the same
structure can be studied, emitted, or certified without making its meaning
depend on the authoring procedure.
-/

open Lean Elab Command
open Lean.Parser.Term

/-! ## Command syntax -/

declare_syntax_cat moduleDesignHeader
syntax "(" ident " : " term ")" : moduleDesignHeader
syntax "(" ident " := " term ")" : moduleDesignHeader

declare_syntax_cat moduleDesignInstanceEntry
syntax ident moduleInstanceModifier* " := " term : moduleDesignInstanceEntry
syntax ident "(" ident " : " term " in " term ")" moduleInstanceModifier*
  " := " term : moduleDesignInstanceEntry

declare_syntax_cat moduleDesignPorts
syntax ident " { " modulePortEntry,* " }" : moduleDesignPorts
syntax ident "(" term ")" "(" ident " := " term ")" : moduleDesignPorts
syntax ident "(" term ")" "(" ident " := " term ")"
  "(" ident " := " term ")" : moduleDesignPorts

declare_syntax_cat moduleDesignInstances
syntax ident " { " moduleDesignInstanceEntry,* " }" : moduleDesignInstances

declare_syntax_cat moduleDesignNamedWireEntry
syntax ident " := " moduleWireSource : moduleDesignNamedWireEntry

declare_syntax_cat moduleDesignNamedWires
syntax "named_wires" " { " moduleDesignNamedWireEntry,* " }" : moduleDesignNamedWires

declare_syntax_cat moduleDesignWiring
syntax ident " { " moduleWireGroup* " }" : moduleDesignWiring

/--
Declare one complete composite hardware design: its typed boundary, concrete
child designs, optional named internal wires, wiring, and recursive emission
naming. An inline `ports`
section generates the ordinary boundary declarations; a `boundary` section
instead reuses an existing typed boundary and its naming. A reused boundary
may additionally provide `namingWith` when the command has component-naming
parameters. The remaining
generated declarations include `instancePorts`, `wiring`, `body`,
`moduleStructure`, `naming`, and the final `design : Naming.NamedModule`.
When component-naming parameters are present, it also generates `namingWith`
and `designWith`; a child's `(naming := ...)` modifier describes how those
parameters propagate through recursive emission without affecting structure.

The emitted module name defaults exactly to the declaration label, and typed
module parameters automatically form its specialization key through
`ToModuleParameter`. The `name`, `variant`, and `specialization` modifiers are
available for exceptional identities. Port and fixed-instance names default
to their labels; indexed child families require an explicit naming expression
because their index need not have a canonical textual form.
The optional `named_wires` section assigns waveform-oriented names to
existing typed sources without changing structural wiring.
Contracts and certifications deliberately remain separate declarations.
-/
syntax (name := moduleDesign)
  "module_design " ident moduleDesignHeader*
    (modulePortsNamingClause)? " where "
    moduleDesignPorts moduleDesignInstances (moduleDesignNamedWires)?
      moduleDesignWiring : command

/-! ## Elaboration -/

private structure ModuleParam where
  name : TSyntax `ident
  type : TSyntax `term
  binder : TSyntax ``Parser.Term.bracketedBinder
  argument : TSyntax `term

private structure FamilyDecl where
  index : TSyntax `ident
  type : TSyntax `term
  enumeration : TSyntax `term

private structure DesignInstanceDecl where
  label : TSyntax `ident
  modifiers : Array (TSyntax `moduleInstanceModifier)
  design : TSyntax `term
  family : Option FamilyDecl
  naming : Option (TSyntax `term)

private def parseParam (param : TSyntax `moduleDesignHeader) :
    CommandElabM ModuleParam :=
  match param with
  | `(moduleDesignHeader| ($name:ident : $type:term)) => do
      pure {
        name
        type
        binder := ← `(bracketedBinder| ($name : $type))
        argument := name
      }
  | _ => throwUnsupportedSyntax

private def parseDesignInstance (entry : TSyntax `moduleDesignInstanceEntry) :
    CommandElabM DesignInstanceDecl :=
  match entry with
  | `(moduleDesignInstanceEntry| $label:ident
      $modifiers:moduleInstanceModifier* := $design:term) => do
      let (modifiers, naming) ← separateNaming modifiers
      pure { label, modifiers, design, family := none, naming }
  | `(moduleDesignInstanceEntry| $label:ident
      ($index:ident : $type:term in $enumeration:term)
      $modifiers:moduleInstanceModifier* := $design:term) => do
      let (modifiers, naming) ← separateNaming modifiers
      pure {
        label, modifiers, design
        family := some { index, type, enumeration }
        naming
      }
  | _ => throwUnsupportedSyntax

where
  separateNaming (modifiers : Array (TSyntax `moduleInstanceModifier)) :
      CommandElabM (Array (TSyntax `moduleInstanceModifier) × Option (TSyntax `term)) := do
    let mut structural := #[]
    let mut naming := none
    for modifier in modifiers do
      let `(moduleInstanceModifier| ($key:ident := $value:term)) := modifier
        | throwUnsupportedSyntax
      if key.getId == `naming then
        if naming.isSome then throwErrorAt key "duplicate `naming` modifier"
        naming := some value
      else structural := structural.push modifier
    pure (structural, naming)

private def structureEntry (decl : DesignInstanceDecl) :
    CommandElabM (TSyntax `moduleInstanceEntry) :=
  match decl.family with
  | none =>
      `(moduleInstanceEntry| $(decl.label):ident
        $(decl.modifiers):moduleInstanceModifier* := ($(decl.design)).moduleStructure)
  | some family =>
      `(moduleInstanceEntry| $(decl.label):ident
        ($(family.index):ident : $(family.type):term in $(family.enumeration):term)
        $(decl.modifiers):moduleInstanceModifier* := ($(decl.design)).moduleStructure)

private def childNamingAlternative (custom : Bool) (decl : DesignInstanceDecl) :
    CommandElabM (TSyntax ``Lean.Parser.Term.matchAlt) := do
  let defaultNaming ← `((($(decl.design))).naming)
  let naming ← if custom then
      match decl.naming with
      | some naming => pure naming
      | none => pure defaultNaming
    else pure defaultNaming
  match decl.family with
  | none =>
      `(matchAltExpr| | .$(decl.label):ident => $naming)
  | some family =>
      `(matchAltExpr| | .$(decl.label):ident $(family.index):ident =>
        $naming)

elab_rules : command
  | `(module_design $designName:ident $headers:moduleDesignHeader*
      $[$namingClause:modulePortsNamingClause]? where
      $portsSection:moduleDesignPorts
      $instancesKeyword:ident { $instanceEntries:moduleDesignInstanceEntry,* }
      $[$namedWiresSection:moduleDesignNamedWires]?
      $wiringKeyword:ident { $wiringGroups:moduleWireGroup* }) => do
    unless instancesKeyword.getId == `instances do
      throwErrorAt instancesKeyword "expected an `instances` section"
    unless wiringKeyword.getId == `wiring do
      throwErrorAt wiringKeyword "expected a `wiring` section"
    let params : Array (TSyntax `moduleDesignHeader) := headers.filter fun header =>
      match header with
      | `(moduleDesignHeader| ($_:ident : $_:term)) => true
      | _ => false
    let modifiers : Array (TSyntax `moduleDesignHeader) := headers.filter fun header =>
      match header with
      | `(moduleDesignHeader| ($_:ident := $_:term)) => true
      | _ => false
    let parsedParams ← params.mapM parseParam
    let binders := parsedParams.map (·.binder)
    let arguments := parsedParams.map (·.argument)
    let portsParams ← parsedParams.mapM fun parameter =>
      `(modulePortsParam| ($(parameter.name) : $(parameter.type)))
    let instancesParams ← parsedParams.mapM fun parameter =>
      `(moduleInstancesParam| ($(parameter.name) : $(parameter.type)))
    let wiringParams ← parsedParams.mapM fun parameter =>
      `(moduleWiringParam| ($(parameter.name) : $(parameter.type)))
    let instanceEntries := instanceEntries.getElems
    if instanceEntries.isEmpty then
      throwErrorAt designName "module_design currently requires at least one child"

    let mut emittedName : Option (TSyntax `term) := none
    let mut emittedVariant : Option (TSyntax `term) := none
    let mut emittedSpecialization : Option (TSyntax `term) := none
    for modifier in modifiers do
      let `(moduleDesignHeader| ($key:ident := $value:term)) := modifier
        | throwUnsupportedSyntax
      if key.getId == `name then
        if emittedName.isSome then throwErrorAt key "duplicate `name` modifier"
        emittedName := some value
      else if key.getId == `variant then
        if emittedVariant.isSome then
          throwErrorAt key "duplicate `variant` modifier"
        emittedVariant := some value
      else if key.getId == `specialization then
        if emittedSpecialization.isSome then
          throwErrorAt key "duplicate `specialization` modifier"
        emittedSpecialization := some value
      else
        throwErrorAt key
          "expected a `name`, `variant`, or `specialization` module modifier"
    let moduleName ← emittedName.getDM do
      pure (Syntax.mkStrLit designName.getId.toString)
    let moduleVariant ← emittedVariant.getDM do
      pure (Syntax.mkStrLit "")
    let moduleSpecialization ← emittedSpecialization.getDM do
      let encoded ← arguments.mapM fun argument =>
        `(Silean.Naming.ModuleParameter.of $argument)
      `([$encoded:term,*])

    let declarations ← instanceEntries.mapM parseDesignInstance
    let structuralEntries ← declarations.mapM structureEntry
    let childNamingAlternatives ← declarations.mapM (childNamingAlternative false)
    let customChildNamingAlternatives ← declarations.mapM (childNamingAlternative true)

    let portsName := mkIdentFrom designName `ports
    let instancePortsName := mkIdentFrom designName `instancePorts
    let contextName := mkIdentFrom designName `context
    let wiringName := mkIdentFrom designName `wiring
    let bodyName := mkIdentFrom designName `body
    let structureName := mkIdentFrom designName `moduleStructure
    let namingName := mkIdentFrom designName `naming
    let namingWithName := mkIdentFrom designName `namingWith
    let bundleName := mkIdentFrom designName `design
    let bundleWithName := mkIdentFrom designName `designWith
    let portsNamingName := mkIdentFrom designName `Naming.ports
    let portsNamingWithName := mkIdentFrom designName `Naming.portsWithNaming
    let instanceNamesName := mkIdentFrom designName `Naming.instanceNames

    elabCommand <| ← `(namespace $designName)
    let (portsTerm, portsNamingTerm, customPortsNaming) ← match portsSection with
      | `(moduleDesignPorts| $portsKeyword:ident {
          $portEntries:modulePortEntry,* }) => do
          unless portsKeyword.getId == `ports do
            throwErrorAt portsKeyword "expected a `ports` section"
          match namingClause with
          | some clause =>
              let `(modulePortsNamingClause|
                  with $namingParams:modulePortsNamingParam,*) := clause
                | throwUnsupportedSyntax
              elabCommand <| ← `(
                module_ports $portsName $portsParams:modulePortsParam*
                  with $namingParams:modulePortsNamingParam,*
                  where $portEntries:modulePortEntry,*
              )
          | none =>
              elabCommand <| ← `(
                module_ports $portsName $portsParams:modulePortsParam*
                  where $portEntries:modulePortEntry,*
              )
          let customPortsNaming : Option (TSyntax `term) ← match namingClause with
            | none => pure none
            | some clause => do
                let `(modulePortsNamingClause|
                    with $namingParams:modulePortsNamingParam,*) := clause
                  | throwUnsupportedSyntax
                let namingArguments ← namingParams.getElems.mapM fun parameter => do
                  match parameter with
                  | `(modulePortsNamingParam|
                      ($name:ident : $_type:term := $_defaultValue:term)) => pure name
                  | _ => throwUnsupportedSyntax
                let custom ← `($portsNamingWithName $arguments:term*
                  $namingArguments:term*)
                pure (some custom)
          pure (← `($portsName $arguments:term*),
            ← `($portsNamingName $arguments:term*), customPortsNaming)
      | `(moduleDesignPorts| $boundaryKeyword:ident ($existingPorts:term)
          ($namingKeyword:ident := $existingNaming:term)) => do
          unless boundaryKeyword.getId == `boundary do
            throwErrorAt boundaryKeyword "expected a `boundary` section"
          unless namingKeyword.getId == `naming do
            throwErrorAt namingKeyword "expected a `naming` modifier"
          if let some clause := namingClause then
            throwErrorAt clause
              "a component-naming clause cannot accompany an existing boundary"
          pure (existingPorts, existingNaming, none)
      | `(moduleDesignPorts| $boundaryKeyword:ident ($existingPorts:term)
          ($namingKeyword:ident := $existingNaming:term)
          ($namingWithKeyword:ident := $existingNamingWith:term)) => do
          unless boundaryKeyword.getId == `boundary do
            throwErrorAt boundaryKeyword "expected a `boundary` section"
          unless namingKeyword.getId == `naming do
            throwErrorAt namingKeyword "expected a `naming` modifier"
          unless namingWithKeyword.getId == `namingWith do
            throwErrorAt namingWithKeyword "expected a `namingWith` modifier"
          if namingClause.isNone then
            throwErrorAt namingWithKeyword
              "`namingWith` requires component-naming parameters"
          pure (existingPorts, existingNaming, some existingNamingWith)
      | _ => throwUnsupportedSyntax
    elabCommand <| ← `(
      module_instances $instancePortsName $instancesParams:moduleInstancesParam*
        for $portsTerm where
        $structuralEntries:moduleInstanceEntry,*
    )
    elabCommand <| ← `(
      module_wiring $wiringName $wiringParams:moduleWiringParam*
        for $contextName $arguments:term* where
        $wiringGroups:moduleWireGroup*
    )
    let namedWireTerms : Array (TSyntax `term) ← match namedWiresSection with
      | none => pure #[]
      | some namedWiresSection => do
          let `(moduleDesignNamedWires| named_wires {
              $entries:moduleDesignNamedWireEntry,* }) := namedWiresSection
            | throwUnsupportedSyntax
          entries.getElems.mapM fun entry => do
            let `(moduleDesignNamedWireEntry| $label:ident :=
                $source:moduleWireSource) := entry
              | throwUnsupportedSyntax
            let contextTerm ← `($contextName $arguments:term*)
            let sourceTerm ← elaborateModuleWireSource contextTerm source
            let wireName := Syntax.mkStrLit label.getId.toString
            `({ signalType := _
                name := $wireName
                source := $sourceTerm })
    let namedWiresTerm ← `(
      ([$namedWireTerms:term,*] :
        List (Silean.Naming.NamedWire ($bodyName $arguments:term*))))
    elabCommand <| ← `(
      def $namingName $binders:bracketedBinder* :
          Silean.Naming.ModuleNaming ($structureName $arguments:term*) := by
        unfold $structureName
        exact .composite ⟨$moduleName, $moduleVariant, $moduleSpecialization⟩
          $portsNamingTerm
          ($instanceNamesName $arguments:term*)
          (fun $childNamingAlternatives:matchAlt*)
          $namedWiresTerm
    )
    if let some customPortsNaming := customPortsNaming then
      let some clause := namingClause
        | throwError "internal error: naming arguments disappeared"
      let `(modulePortsNamingClause| with $namingParams:modulePortsNamingParam,*) := clause
        | throwUnsupportedSyntax
      let namingBinders ← namingParams.getElems.mapM fun parameter => do
        match parameter with
        | `(modulePortsNamingParam|
            ($name:ident : $type:term := $_defaultValue:term)) =>
            `(bracketedBinder| ($name : $type))
        | _ => throwUnsupportedSyntax
      let namingArguments ← namingParams.getElems.mapM fun parameter => do
        match parameter with
        | `(modulePortsNamingParam|
            ($name:ident : $_type:term := $_defaultValue:term)) => pure name
        | _ => throwUnsupportedSyntax
      elabCommand <| ← `(
        def $namingWithName $binders:bracketedBinder*
            $namingBinders:bracketedBinder* :
            Silean.Naming.ModuleNaming ($structureName $arguments:term*) := by
          unfold $structureName
          exact .composite ⟨$moduleName, $moduleVariant, $moduleSpecialization⟩
            $customPortsNaming
            ($instanceNamesName $arguments:term*)
            (fun $customChildNamingAlternatives:matchAlt*)
            $namedWiresTerm
      )
      elabCommand <| ← `(
        @[reducible] def $bundleWithName $binders:bracketedBinder*
            $namingBinders:bracketedBinder* : Silean.Naming.NamedModule :=
          ⟨$portsTerm, $structureName $arguments:term*,
            $namingWithName $arguments:term* $namingArguments:term*⟩
      )
    elabCommand <| ← `(
      @[reducible] def $bundleName $binders:bracketedBinder* :
          Silean.Naming.NamedModule :=
        ⟨$portsTerm, $structureName $arguments:term*,
          $namingName $arguments:term*⟩
    )
    elabCommand <| ← `(end $designName)

end Silean.Authoring
