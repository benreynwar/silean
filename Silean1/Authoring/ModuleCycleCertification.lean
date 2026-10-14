import Silean.Contracts.Cycle.CycleLayerConstruction

namespace Silean.Authoring

/-! # Assembling cycle certification

`module_cycle_certification` is the final proof-side authoring step for a
composite module. It combines certified children, validated rule schedules, a
state-correspondence relation, its coverage proof, and a module-specific
implementation proof. From these ingredients it generates a reusable
`ModuleCycleCertifiedLayer`, the certification of the chosen concrete
structure, and the public certified module bundle.

The command packages evidence rather than inventing it: the behavioral
implementation proof and state correspondence remain explicit Lean
definitions supplied by the module author. Existence and uniqueness of the
structural solution are obtained generically from the checked schedules and
the child certifications.
-/

open Lean Elab Command
open Lean.Parser.Term

/-! ## Command syntax -/

declare_syntax_cat moduleCycleCertificationParam
syntax "(" ident " : " term ")" : moduleCycleCertificationParam

declare_syntax_cat moduleCycleCertificationItem
syntax ident " := " term : moduleCycleCertificationItem

/-- Generate the standard public bridge from structural realizability to the
module's cycle contract. This is also useful for certifications assembled
without `module_cycle_certification`. -/
syntax (name := moduleCycleRealizationBridge)
    "module_cycle_realization_bridge " ident moduleCycleCertificationParam*
    " for " term " implementing " term " using " term : command

/-- Assemble a validated rule schedule and a module-specific implementation
proof into the standard certified layer, concrete certification, and public
certified bundle. The state relation and behavioral proof remain explicit. -/
syntax (name := moduleCycleCertification)
    "module_cycle_certification " ident moduleCycleCertificationParam*
    " for " term " via " term " with " term " implementing " term " where "
    moduleCycleCertificationItem,* : command

/-! ## Elaboration -/

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

private def emitRealizationBridge (theoremName : TSyntax `ident)
    (parameters : Array (TSyntax `moduleCycleCertificationParam))
    (moduleStructure contract certification : TSyntax `term) : CommandElabM Unit := do
  let params ← parameters.mapM parseParam
  let binders := params.map (·.binder)
  let arguments := params.map (·.argument)
  elabCommand <| ← `(
    /-- Every realizable structural boundary step is accepted by the public
    cycle contract for some corresponding behavioral states. -/
    theorem $theoremName $binders:bracketedBinder*
        {structuralStep : ($moduleStructure).Step}
        (realizes : ($moduleStructure).Realizes structuralStep) :
        ∃ currentState nextState,
          ($contract).Allows {
            inputs := structuralStep.inputs
            currentState := currentState
            outputs := structuralStep.outputs
            nextState := nextState } := by
      obtain ⟨currentState, corresponds⟩ :=
        ($certification $arguments:term*).hasCorrespondingState
          structuralStep.currentState
      obtain ⟨nextState, allowed, _⟩ :=
        ($certification $arguments:term*).allows_of_realizes
          currentState structuralStep corresponds realizes
      exact ⟨currentState, nextState, allowed⟩
  )

elab_rules : command
  | `(module_cycle_realization_bridge $theoremName:ident
      $parameters:moduleCycleCertificationParam* for $moduleStructure:term
      implementing $contract:term using $certification:term) =>
    emitRealizationBridge theoremName parameters moduleStructure contract certification

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
    let allowedOfRealization :=
      mkIdentFrom certificationName `allowed_of_realization
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
    elabCommand <| ← `(
      module_cycle_realization_bridge $allowedOfRealization
        $parameters:moduleCycleCertificationParam* for $moduleStructure
        implementing $contract using $certificationName
    )

end Silean.Authoring
