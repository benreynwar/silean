import Silean.Contracts.Cycle.CycleLayerConstruction

namespace Silean.Authoring

open Lean Elab Command
open Lean.Parser.Term

declare_syntax_cat moduleCycleCertificationParam
syntax "(" ident " : " term ")" : moduleCycleCertificationParam

declare_syntax_cat moduleCycleCertificationItem
syntax ident " := " term : moduleCycleCertificationItem

/-- Assemble a validated rule schedule and a module-specific implementation
proof into the standard certified layer, concrete certification, and public
certified bundle. The state relation and behavioral proof remain explicit. -/
syntax (name := moduleCycleCertification)
    "module_cycle_certification " ident moduleCycleCertificationParam*
    " for " term " via " term " with " term " implementing " term " where "
    moduleCycleCertificationItem,* : command

private structure CertificationParam where
  binder : TSyntax ``Parser.Term.bracketedBinder
  argument : TSyntax `term

private structure CertificationItems where
  schedules : TSyntax `term
  structuralChildren : TSyntax `term
  certifiedChildren : TSyntax `term
  structuresMatch : TSyntax `term
  stateCorresponds : TSyntax `term
  stateCoverage : TSyntax `term
  implements : TSyntax `term

private def parseParam (parameter : TSyntax `moduleCycleCertificationParam) :
    CommandElabM CertificationParam :=
  match parameter with
  | `(moduleCycleCertificationParam| ($name:ident : $type:term)) => do
      pure {
        binder := ← `(bracketedBinder| ($name : $type))
        argument := name
      }
  | _ => throwUnsupportedSyntax

private def parseItem (item : TSyntax `moduleCycleCertificationItem) :
    CommandElabM (Name × TSyntax `term × Syntax) :=
  match item with
  | `(moduleCycleCertificationItem| $name:ident := $value:term) =>
      pure (name.getId, value, name)
  | _ => throwUnsupportedSyntax

private def collectItems (syntaxItems : Array (TSyntax `moduleCycleCertificationItem)) :
    CommandElabM CertificationItems := do
  let expected := [`schedules, `structuralChildren, `certifiedChildren,
    `structuresMatch, `stateCorresponds, `stateCoverage, `implements]
  let mut values : NameMap (TSyntax `term × Syntax) := {}
  for item in syntaxItems do
    let (name, value, source) ← parseItem item
    unless expected.contains name do
      throwErrorAt source "unknown certification item `{name}`"
    if values.contains name then
      throwErrorAt source "duplicate certification item `{name}`"
    values := values.insert name (value, source)
  let get (name : Name) : CommandElabM (TSyntax `term) :=
    match values.find? name with
    | some (value, _) => pure value
    | none => throwError "module_cycle_certification requires `{name} := ...`"
  return {
    schedules := ← get `schedules
    structuralChildren := ← get `structuralChildren
    certifiedChildren := ← get `certifiedChildren
    structuresMatch := ← get `structuresMatch
    stateCorresponds := ← get `stateCorresponds
    stateCoverage := ← get `stateCoverage
    implements := ← get `implements
  }

elab_rules : command
  | `(module_cycle_certification $certificationName:ident
      $parameters:moduleCycleCertificationParam* for $moduleStructure:term via
      $body:term with $childContracts:term implementing $contract:term where
      $syntaxItems:moduleCycleCertificationItem,*) => do
    let params ← parameters.mapM parseParam
    let binders := params.map (·.binder)
    let arguments := params.map (·.argument)
    let items ← collectItems syntaxItems.getElems
    let layerName := mkIdentFrom certificationName `certifiedLayer
    let bundleName := mkIdentFrom certificationName `certified
    let moduleStructureTheorem :=
      mkIdentFrom certificationName `certified_moduleStructure
    let contractTheorem := mkIdentFrom certificationName `certified_cycleContract
    elabCommand <| ← `(
      noncomputable opaque $layerName $binders:bracketedBinder* :
          Silean.Contracts.Cycle.ModuleCycleCertifiedLayer
            ($body) ($childContracts) ($contract) :=
        Silean.Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
          ($(items.schedules)).schedules ($(items.schedules)).coversChildren
          $(items.stateCorresponds) $(items.stateCoverage) $(items.implements)
    )
    elabCommand <| ← `(
      noncomputable opaque $certificationName $binders:bracketedBinder* :
          Silean.Contracts.Cycle.ModuleCycleCertification
            ($moduleStructure) ($contract) :=
        ($layerName $arguments:term*).certifyComposite
          $(items.structuralChildren) $(items.certifiedChildren)
          $(items.structuresMatch)
    )
    elabCommand <| ← `(
      noncomputable def $bundleName $binders:bracketedBinder* :=
        ($certificationName $arguments:term*).bundle
    )
    elabCommand <| ← `(
      @[simp] theorem $moduleStructureTheorem $binders:bracketedBinder* :
          ($bundleName $arguments:term*).moduleStructure = $moduleStructure := rfl
    )
    elabCommand <| ← `(
      @[simp] theorem $contractTheorem $binders:bracketedBinder* :
          ($bundleName $arguments:term*).cycleContract = $contract := rfl
    )

end Silean.Authoring
