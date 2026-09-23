import Silean.Authoring.ModulePorts
import Silean.Structure.ModuleBody

namespace Silean.Authoring

/-! # Child instance authoring

`module_instances` declares the child interfaces at one structural layer. A
child may supply either a concrete `ModuleStructure` or only its `ModulePorts`.
The command always generates the child-name type and enumeration, each child's
ports, the layer's `EndpointContext`, and emitted instance names. It generates
the selected `ModuleStructure`s only when every child is concrete. Fixed
children and indexed child families use the same dependent `InstancePorts`
representation.

This is the interface side of hierarchy construction. Concrete entries also
choose actual child structures, but no entry says anything about behavioral
contracts or proofs. `module_design` normally invokes this command, while
`module_child_certifications` later associates those same children with
certification evidence.
-/

open Lean Elab Command Meta
open Lean.Parser.Term

/-! ## Command syntax -/

declare_syntax_cat moduleInstanceModifier
syntax "(" ident " := " term ")" : moduleInstanceModifier

declare_syntax_cat moduleInstancesParam
syntax "(" ident " : " term ")" : moduleInstancesParam

declare_syntax_cat moduleInstanceEntry
syntax ident moduleInstanceModifier* " := " term : moduleInstanceEntry
syntax ident "(" ident " : " term " in " term ")" moduleInstanceModifier*
  " := " term : moduleInstanceEntry
syntax ident moduleInstanceModifier* " : " term : moduleInstanceEntry
syntax ident "(" ident " : " term " in " term ")" moduleInstanceModifier*
  " : " term : moduleInstanceEntry

/--
Declare the children of an ordinary structural layer from concrete hardware
structures (`child := structure`) or unresolved interfaces (`child : ports`).
The command always generates instance labels and ports, the endpoint context,
and emitted instance names. It generates `structuralChildren` only when every
entry is concrete. Contracts and certifications are associated separately by
`module_child_certifications` in proof-oriented code. An indexed entry supplies
its index type and executable enumeration.
-/
syntax (name := moduleInstances)
  "module_instances " ident moduleInstancesParam* " for " term " where "
    moduleInstanceEntry,* : command

/-! ## Elaboration -/

private structure FamilyDecl where
  index : TSyntax `ident
  type : TSyntax `term
  enumeration : TSyntax `term

private structure InstanceDecl where
  label : TSyntax `ident
  sourceName : TSyntax `term
  moduleStructure : Option (TSyntax `term)
  ports : TSyntax `term
  family : Option FamilyDecl

private structure ModuleParam where
  binder : TSyntax ``Parser.Term.bracketedBinder
  funBinder : TSyntax ``Parser.Term.funBinder
  argument : TSyntax `term
  name : Name

private partial def mentionsName (name : Name) (stx : Syntax) : Bool :=
  if stx.isIdent then stx.getId == name
  else stx.getArgs.any (mentionsName name)

private def structurePorts (binders : Array (TSyntax ``Parser.Term.funBinder))
    (moduleStructure : TSyntax `term) : CommandElabM (TSyntax `term) := do
  liftTermElabM do
    let lambda ← `(fun $binders:funBinder* => $moduleStructure)
    let value ← Term.elabTerm lambda none
    Term.synthesizeSyntheticMVarsNoPostponing
    let rawType ← instantiateMVars (← inferType value)
    liftMetaM <| forallTelescope rawType fun _ resultType => do
      let type ← whnf resultType
      let function := type.getAppFn
      unless function.isConstOf ``Silean.ModuleStructure do
        throwErrorAt moduleStructure
          "expected a ModuleStructure; the supplied term has type {type}"
      let arguments := type.getAppArgs
      unless arguments.size == 1 do
        throwErrorAt moduleStructure "unexpected ModuleStructure type shape"
      let ports ← PrettyPrinter.delab arguments[0]!
      pure ports

private def parseInstanceDecl (binders : Array (TSyntax ``Parser.Term.funBinder))
    (entry : TSyntax `moduleInstanceEntry) :
    CommandElabM InstanceDecl := do
  let (label, family, modifiers, moduleStructure, directPorts) ← match entry with
    | `(moduleInstanceEntry| $label:ident $modifiers:moduleInstanceModifier*
        := $moduleStructure:term) =>
        pure (label, none, modifiers, some moduleStructure, none)
    | `(moduleInstanceEntry| $label:ident
        ($index:ident : $type:term in $enumeration:term)
        $modifiers:moduleInstanceModifier* := $moduleStructure:term) =>
        pure (label, some { index, type, enumeration }, modifiers,
          some moduleStructure, none)
    | `(moduleInstanceEntry| $label:ident $modifiers:moduleInstanceModifier*
        : $ports:term) =>
        pure (label, none, modifiers, none, some ports)
    | `(moduleInstanceEntry| $label:ident
        ($index:ident : $type:term in $enumeration:term)
        $modifiers:moduleInstanceModifier* : $ports:term) =>
        pure (label, some { index, type, enumeration }, modifiers,
          none, some ports)
    | _ => throwUnsupportedSyntax
  let mut sourceName : Option (TSyntax `term) := none
  for modifier in modifiers do
    let `(moduleInstanceModifier| ($key:ident := $value:term)) := modifier
      | throwUnsupportedSyntax
    unless key.getId == `name do
      throwErrorAt key "expected a `name` instance modifier"
    if sourceName.isSome then throwErrorAt key "duplicate `name` modifier"
    sourceName := some value
  let resolvedSourceName ← match sourceName with
    | some value => `(($value : Silean.Naming.SourceName))
    | none =>
        if family.isSome then
          throwErrorAt label "an indexed child family requires a `name` modifier"
        let literal := Syntax.mkStrLit label.getId.toString
        `(($literal : Silean.Naming.SourceName))
  let familyBinders ← match family with
    | none => pure binders
    | some family => do
        let binder ← `(funBinder| ($(family.index) : $(family.type)))
        pure (binders.push binder)
  let ports ← match moduleStructure, directPorts with
    | some moduleStructure, none => structurePorts familyBinders moduleStructure
    | none, some ports => pure ports
    | _, _ => throwError "internal error: invalid child implementation choice"
  pure {
    label := label
    sourceName := resolvedSourceName
    moduleStructure := moduleStructure
    ports := ports
    family := family
  }

private def parseParam (param : TSyntax `moduleInstancesParam) :
    CommandElabM ModuleParam :=
  match param with
  | `(moduleInstancesParam| ($name:ident : $type:term)) => do
      pure {
        binder := ← `(bracketedBinder| ($name : $type))
        funBinder := ← `(funBinder| ($name : $type))
        argument := name
        name := name.getId
      }
  | _ => throwUnsupportedSyntax

private def constructorSyntax (decl : InstanceDecl) :
    CommandElabM (TSyntax ``Parser.Command.ctor) := do
  match decl.family with
  | none => `(Parser.Command.ctor| | $(decl.label):ident)
  | some family =>
      `(Parser.Command.ctor| | $(decl.label):ident
        ($(family.index) : $(family.type)))

private def instancePattern (decl : InstanceDecl) : CommandElabM (TSyntax `term) :=
  match decl.family with
  | none => `(.$(decl.label):ident)
  | some family => `(.$(decl.label):ident $(family.index))

private def portsAlternative (decl : InstanceDecl) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) := do
  let pattern ← instancePattern decl
  `(matchAltExpr| | $pattern => $(decl.ports))

private def nameAlternative (decl : InstanceDecl) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) := do
  let pattern ← instancePattern decl
  `(matchAltExpr| | $pattern => $(decl.sourceName))

private def structureAlternative (decl : InstanceDecl) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) := do
  let pattern ← instancePattern decl
  let some moduleStructure := decl.moduleStructure
    | throwErrorAt decl.label "unresolved child has no ModuleStructure"
  `(matchAltExpr| | $pattern => $moduleStructure)

private def representationPayloadType (decl : InstanceDecl) : CommandElabM (TSyntax `term) :=
  match decl.family with
  | none => `(PUnit)
  | some family => pure family.type

private def representationPayloadEnumeration (decl : InstanceDecl) :
    CommandElabM (TSyntax `term) :=
  match decl.family with
  | none => `(Silean.Enumeration.punit)
  | some family => pure family.enumeration

private def representationType : List InstanceDecl → CommandElabM (TSyntax `term)
  | [] => throwError "module_instances requires at least one child"
  | [decl] => representationPayloadType decl
  | decl :: rest => do
      `(Sum $(← representationPayloadType decl) $(← representationType rest))

private def representationEnumeration : List InstanceDecl → CommandElabM (TSyntax `term)
  | [] => throwError "module_instances requires at least one child"
  | [decl] => representationPayloadEnumeration decl
  | decl :: rest => do
      `(Silean.Enumeration.sum $(← representationPayloadEnumeration decl)
        $(← representationEnumeration rest))

private def forwardMapper (decl : InstanceDecl) : CommandElabM (TSyntax `term) :=
  match decl.family with
  | none => `(fun _ => .$(decl.label):ident)
  | some family => `(fun $(family.index) => .$(decl.label):ident $(family.index))

private def representationForward : List InstanceDecl → CommandElabM (TSyntax `term)
  | [] => throwError "module_instances requires at least one child"
  | [decl] => forwardMapper decl
  | decl :: rest => do
      `(Sum.elim $(← forwardMapper decl) $(← representationForward rest))

private def encodedPayload (position last : Nat) (payload : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  let mut result := payload
  if position < last then result ← `(.inl $result)
  for _ in [:position] do result ← `(.inr $result)
  pure result

private def backwardAlternative (decl : InstanceDecl) (position last : Nat) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) := do
  let pattern ← instancePattern decl
  let payload ← match decl.family with
    | none => `(.unit)
    | some family => pure family.index
  let encoded ← encodedPayload position last payload
  `(matchAltExpr| | $pattern => $encoded)

private def leftInverseAlternative (decl : InstanceDecl) (position last : Nat) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) := do
  let payload ← match decl.family with
    | some family => pure family.index
    | none => pure <| mkIdentFrom decl.label (decl.label.getId.appendAfter "Value")
  let pattern ← encodedPayload position last payload
  let proof ← match decl.family with
    | some _ => `(by rfl)
    | none => `(by cases $payload:ident; rfl)
  `(matchAltExpr| | $pattern => $proof)

private def rightInverseAlternative (decl : InstanceDecl) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) := do
  let pattern ← instancePattern decl
  `(matchAltExpr| | $pattern => by rfl)

elab_rules : command
  | `(module_instances $instancePortsName:ident $params:moduleInstancesParam*
        for $parentPorts:term where
        $entries:moduleInstanceEntry,*) => do
    let entries := entries.getElems
    if entries.isEmpty then
      throwErrorAt instancePortsName
        "module_instances currently requires at least one child"
    let parsedParams ← params.mapM parseParam
    let binders := parsedParams.map (·.binder)
    let funBinders := parsedParams.map (·.funBinder)
    let arguments := parsedParams.map (·.argument)
    let declarations ← entries.mapM (parseInstanceDecl funBinders)
    let hasFamilies := declarations.any (·.family.isSome)
    let instanceParams := parsedParams.filter fun parameter =>
      declarations.any fun declaration =>
        declaration.family.any fun family =>
          mentionsName parameter.name family.type.raw
    let instanceBinders := instanceParams.map (·.binder)
    let instanceArguments := instanceParams.map (·.argument)
    let enumerationParams := parsedParams.filter fun parameter =>
      declarations.any fun declaration =>
        declaration.family.any fun family =>
          mentionsName parameter.name family.type.raw ||
            mentionsName parameter.name family.enumeration.raw
    let enumerationBinders := enumerationParams.map (·.binder)
    let enumerationArguments := enumerationParams.map (·.argument)
    let constructors ← declarations.mapM constructorSyntax
    let portAlternatives ← declarations.mapM portsAlternative
    let nameAlternatives ← declarations.mapM nameAlternative
    let allConcrete := declarations.all fun declaration =>
      declaration.moduleStructure.isSome

    let instanceIdent := mkIdentFrom instancePortsName `Instance
    let instanceRepresentationIdent :=
      mkIdentFrom instancePortsName `InstanceRepresentation
    let instanceRepresentationEnumerationIdent :=
      mkIdentFrom instancePortsName `instanceRepresentationEnumeration
    let instanceForwardIdent := mkIdentFrom instancePortsName `instanceForward
    let instanceBackwardIdent := mkIdentFrom instancePortsName `instanceBackward
    let instanceLeftInverseIdent := mkIdentFrom instancePortsName `instanceLeftInverse
    let instanceRightInverseIdent := mkIdentFrom instancePortsName `instanceRightInverse
    let instanceEnumerationIdent := mkIdentFrom instancePortsName `instanceEnumeration
    let contextIdent := mkIdentFrom instancePortsName `context
    let structuralChildrenIdent := mkIdentFrom instancePortsName `structuralChildren
    let instanceNamesIdent := mkIdentFrom instancePortsName `Naming.instanceNames

    let instanceType : TSyntax `term ← if hasFamilies then
      `($instanceIdent $instanceArguments:term*)
    else
      `($instanceIdent)

    if hasFamilies then
      elabCommand <| ← `(
        inductive $instanceIdent $instanceBinders:bracketedBinder* where
          $constructors:ctor*
      )
      let declarationList := declarations.toList
      let representation ← representationType declarationList
      let representationValues ← representationEnumeration declarationList
      let forward ← representationForward declarationList
      let last := declarations.size - 1
      let backwardAlternatives ← declarations.mapIdxM fun position declaration =>
        backwardAlternative declaration position last
      let leftInverseAlternatives ← declarations.mapIdxM fun position declaration =>
        leftInverseAlternative declaration position last
      let rightInverseAlternatives ← declarations.mapM rightInverseAlternative
      elabCommand <| ← `(
        private abbrev $instanceRepresentationIdent
            $enumerationBinders:bracketedBinder* : Type :=
          $representation
      )
      elabCommand <| ← `(
        @[reducible] private def $instanceRepresentationEnumerationIdent
            $enumerationBinders:bracketedBinder* :
            Silean.Enumeration
              ($instanceRepresentationIdent $enumerationArguments:term*) :=
          $representationValues
      )
      elabCommand <| ← `(
        private def $instanceForwardIdent $enumerationBinders:bracketedBinder* :
            $instanceRepresentationIdent $enumerationArguments:term* → $instanceType :=
          $forward
      )
      elabCommand <| ← `(
        private def $instanceBackwardIdent $enumerationBinders:bracketedBinder* :
            $instanceType → $instanceRepresentationIdent $enumerationArguments:term*
          $backwardAlternatives:matchAlt*
      )
      elabCommand <| ← `(
        private theorem $instanceLeftInverseIdent $enumerationBinders:bracketedBinder*
            (value : $instanceRepresentationIdent $enumerationArguments:term*) :
            $instanceBackwardIdent $enumerationArguments:term*
                ($instanceForwardIdent $enumerationArguments:term* value) = value :=
          match value with $leftInverseAlternatives:matchAlt*
      )
      elabCommand <| ← `(
        private theorem $instanceRightInverseIdent $enumerationBinders:bracketedBinder*
            (value : $instanceType) :
            $instanceForwardIdent $enumerationArguments:term*
                ($instanceBackwardIdent $enumerationArguments:term* value) = value :=
          match value with $rightInverseAlternatives:matchAlt*
      )
      elabCommand <| ← `(
        @[reducible] private def $instanceEnumerationIdent
            $enumerationBinders:bracketedBinder* : Silean.Enumeration $instanceType :=
          Silean.Enumeration.relabel
            ($instanceRepresentationEnumerationIdent $enumerationArguments:term*)
            ($instanceForwardIdent $enumerationArguments:term*)
            ($instanceBackwardIdent $enumerationArguments:term*)
            ($instanceLeftInverseIdent $enumerationArguments:term*)
            ($instanceRightInverseIdent $enumerationArguments:term*)
      )
      elabCommand <| ← `(
        @[reducible] private instance $enumerationBinders:bracketedBinder* :
            Silean.Enumeration $instanceType :=
          $instanceEnumerationIdent $enumerationArguments:term*
      )
    else
      elabCommand <| ← `(
        inductive $instanceIdent where
          $constructors:ctor*
        deriving Silean.Enumeration
      )
    if hasFamilies then
      elabCommand <| ← `(
        @[reducible] def $instancePortsName $binders:bracketedBinder* :
            Silean.InstancePorts where
          Key := $instanceType
          keys := $instanceEnumerationIdent $enumerationArguments:term*
          value := fun $portAlternatives:matchAlt*
      )
    else
      elabCommand <| ← `(
        @[reducible] def $instancePortsName $binders:bracketedBinder* :
            Silean.InstancePorts :=
          Silean.EnumeratedMap.of $instanceType fun $portAlternatives:matchAlt*
      )
    elabCommand <| ← `(
      @[reducible] def $contextIdent $binders:bracketedBinder* :
          Silean.EndpointContext where
        ports := $parentPorts
        instancePorts := $instancePortsName $arguments:term*
    )
    if allConcrete then
      let structureAlternatives ← declarations.mapM structureAlternative
      elabCommand <| ← `(
        @[reducible] def $structuralChildrenIdent $binders:bracketedBinder*
            (child : ($instancePortsName $arguments:term*).Name) :
            Silean.ModuleStructure
              (($instancePortsName $arguments:term*).ports child) :=
          match child with $structureAlternatives:matchAlt*
      )
    elabCommand <| ← `(
      @[reducible, simp] private def $instanceNamesIdent $binders:bracketedBinder*
          (child : ($instancePortsName $arguments:term*).Name) :
          Silean.Naming.SourceName :=
        match child with $nameAlternatives:matchAlt*
    )

end Silean.Authoring
