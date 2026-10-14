import Silean.Authoring.ModuleInstances
import Silean.Contracts.Cycle.CycleImplementation

namespace Silean.Authoring

/-! # Associating certified child modules

`module_child_certifications` is the first proof-side step for a composite
design. For every child named by a `ModuleBody`, it records a
`ModuleCycleCertification`. The certification's dependent type determines both
the child's boundary contract and its concrete structure.

The command generates the family of child contracts, the corresponding
certified child structures, and a theorem that those structures are exactly
the children selected earlier by `module_instances` or `module_design`. These
declarations are then consumed by rule scheduling and final cycle
certification; they do not alter the design-side hierarchy.
-/

open Lean Elab Command Meta
open Lean.Parser.Term

/-! ## Command syntax -/

declare_syntax_cat moduleChildCertificationParam
syntax "(" ident " : " term ")" : moduleChildCertificationParam

declare_syntax_cat moduleChildCertificationEntry
syntax ident " := " term : moduleChildCertificationEntry
syntax ident "(" ident " : " term ")" " := " term :
  moduleChildCertificationEntry

/--
Associate the children of an already declared structural layer with cycle
contracts and certifications. Each entry is one `ModuleCycleCertification`;
its dependent type is the sole source of the exact child structure and chosen
contract. This proof-side declaration generates
`childContracts`, `certifiedChildren`, and the proof that the certified child
structures are exactly those selected by the design-side `module_instances`.
-/
syntax (name := moduleChildCertifications)
  "module_child_certifications " ident moduleChildCertificationParam*
    " for " term " where " moduleChildCertificationEntry,* : command

/-! ## Elaboration -/

private structure ModuleParam where
  binder : TSyntax ``Parser.Term.bracketedBinder
  funBinder : TSyntax ``Parser.Term.funBinder
  argument : TSyntax `term

private structure CertificationDecl where
  label : TSyntax `ident
  index : Option (TSyntax `ident)
  indexType : Option (TSyntax `term)
  certification : TSyntax `term
  moduleStructure : TSyntax `term
  contract : TSyntax `term

private def parseParam (param : TSyntax `moduleChildCertificationParam) :
    CommandElabM ModuleParam :=
  match param with
  | `(moduleChildCertificationParam| ($name:ident : $type:term)) => do
      pure {
        binder := ← `(bracketedBinder| ($name : $type))
        funBinder := ← `(funBinder| ($name : $type))
        argument := name
      }
  | _ => throwUnsupportedSyntax

private def certificationIndices
    (binders : Array (TSyntax ``Parser.Term.funBinder))
    (certification : TSyntax `term) :
    CommandElabM (TSyntax `term × TSyntax `term) := do
  liftTermElabM do
    let lambda ← `(fun $binders:funBinder* => $certification)
    let value ← Term.elabTerm lambda none
    Term.synthesizeSyntheticMVarsNoPostponing
    let rawType ← instantiateMVars (← inferType value)
    liftMetaM <| forallTelescope rawType fun _ resultType => do
      let type ← whnf resultType
      unless type.getAppFn.isConstOf
          ``Silean.Contracts.Cycle.ModuleCycleCertification do
        throwErrorAt certification
          "expected a ModuleCycleCertification; the supplied term has type {type}"
      let arguments := type.getAppArgs
      unless arguments.size == 3 do
        throwErrorAt certification "unexpected ModuleCycleCertification type shape"
      pure (← PrettyPrinter.delab arguments[1]!,
        ← PrettyPrinter.delab arguments[2]!)

private def parseDecl (binders : Array (TSyntax ``Parser.Term.funBinder))
    (entry : TSyntax `moduleChildCertificationEntry) :
    CommandElabM CertificationDecl := do
  let (label, index, indexType, certification) ← match entry with
    | `(moduleChildCertificationEntry| $label:ident := $certification:term) =>
        pure (label, none, none, certification)
    | `(moduleChildCertificationEntry| $label:ident
        ($index:ident : $indexType:term) := $certification:term) =>
        pure (label, some index, some indexType, certification)
    | _ => throwUnsupportedSyntax
  let certificateBinders ← match index, indexType with
    | some index, some indexType =>
        pure <| binders.push (← `(funBinder| ($index : $indexType)))
    | none, none => pure binders
    | _, _ => throwUnsupportedSyntax
  let (moduleStructure, contract) ←
    certificationIndices certificateBinders certification
  pure { label, index, indexType, certification, moduleStructure, contract }

private def childPattern (decl : CertificationDecl) :
    CommandElabM (TSyntax `term) :=
  match decl.index with
  | none => `(.$(decl.label):ident)
  | some index => `(.$(decl.label):ident $index)

private def contractAlternative (decl : CertificationDecl) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) := do
  let pattern ← childPattern decl
  `(matchAltExpr| | $pattern => $(decl.contract))

private def certifiedAlternative (decl : CertificationDecl) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) := do
  let pattern ← childPattern decl
  `(matchAltExpr| | $pattern =>
    ⟨$(decl.moduleStructure), $(decl.certification)⟩)

elab_rules : command
  | `(module_child_certifications $childContractsName:ident
        $params:moduleChildCertificationParam* for $body:term where
        $entries:moduleChildCertificationEntry,*) => do
    let entries := entries.getElems
    if entries.isEmpty then
      throwErrorAt childContractsName
        "module_child_certifications requires at least one child"
    let parsedParams ← params.mapM parseParam
    let binders := parsedParams.map (·.binder)
    let funBinders := parsedParams.map (·.funBinder)
    let arguments := parsedParams.map (·.argument)
    let declarations ← entries.mapM (parseDecl funBinders)
    let mut seenLabels : List Name := []
    for declaration in declarations do
      if seenLabels.contains declaration.label.getId then
        throwErrorAt declaration.label
          "duplicate child certification for `{declaration.label.getId}`"
      seenLabels := declaration.label.getId :: seenLabels
    let contractAlternatives ← declarations.mapM contractAlternative
    let certifiedAlternatives ← declarations.mapM certifiedAlternative
    let certifiedChildrenName := mkIdentFrom childContractsName `certifiedChildren
    let structuralChildrenName := mkIdentFrom childContractsName `structuralChildren
    let structuresMatchName :=
      mkIdentFrom childContractsName `certifiedChildren_moduleStructure

    elabCommand <| ← `(
      @[reducible] private def $childContractsName $binders:bracketedBinder* :
          Silean.Contracts.Cycle.ChildCycleContracts $body :=
        fun child => match child with $contractAlternatives:matchAlt*
    )
    elabCommand <| ← `(
      @[reducible] private noncomputable def $certifiedChildrenName
          $binders:bracketedBinder*
          (child : ($body).instancePorts.Name) :
          Silean.Contracts.Cycle.ModuleCycleCertifiedStructure
            ($childContractsName $arguments:term* child) :=
        match child with $certifiedAlternatives:matchAlt*
    )
    elabCommand <| ← `(
      private theorem $structuresMatchName $binders:bracketedBinder*
          (child : ($body).instancePorts.Name) :
          ($certifiedChildrenName $arguments:term* child).moduleStructure =
            $structuralChildrenName $arguments:term* child := by
        cases child <;> rfl
    )

end Silean.Authoring
