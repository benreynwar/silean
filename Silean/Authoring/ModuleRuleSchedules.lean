import Silean.Contracts.Cycle.CycleScheduleDerivation

namespace Silean.Authoring

open Lean Elab Command
open Lean.Parser.Term

declare_syntax_cat moduleRuleScheduleParam
syntax "(" ident " : " term ")" : moduleRuleScheduleParam

declare_syntax_cat moduleRuleOccurrence
syntax term " => " term : moduleRuleOccurrence
syntax "{" term,* "}" " => " term : moduleRuleOccurrence

declare_syntax_cat moduleRuleOrder
syntax "[" moduleRuleOccurrence,* "]" : moduleRuleOrder
syntax "from" "(" term ")" : moduleRuleOrder

declare_syntax_cat moduleOutputSchedule
syntax "|" term " => " moduleRuleOrder : moduleOutputSchedule

/-- Declare the visible ordering of child rules and derive its validity proof.
Literal schedules use `child => rule`; `{child₁, child₂} => rule` applies one
rule to a consecutive group; and `from (...)` retains ordinary Lean for
indexed, mapped, or concatenated rule families. -/
syntax (name := moduleRuleSchedules)
    "module_rule_schedules " ident moduleRuleScheduleParam*
    " for " term " with " term " implementing " term " where "
    ident moduleOutputSchedule+ ident " := " moduleRuleOrder : command

private structure ScheduleParam where
  binder : TSyntax ``Parser.Term.bracketedBinder
  argument : TSyntax `term

private def parseParam (parameter : TSyntax `moduleRuleScheduleParam) :
    CommandElabM ScheduleParam :=
  match parameter with
  | `(moduleRuleScheduleParam| ($name:ident : $type:term)) => do
      pure {
        binder := ← `(bracketedBinder| ($name : $type))
        argument := name
      }
  | _ => throwUnsupportedSyntax

private def occurrenceTerms (occurrence : TSyntax `moduleRuleOccurrence) :
    CommandElabM (Array (TSyntax `term)) :=
  match occurrence with
  | `(moduleRuleOccurrence| $child:term => $rule:term) => do
      pure #[← `(⟨$child, $rule⟩)]
  | `(moduleRuleOccurrence| {$children:term,*} => $rule:term) =>
      children.getElems.mapM fun child => `(⟨$child, $rule⟩)
  | _ => throwUnsupportedSyntax

private def orderTerm (order : TSyntax `moduleRuleOrder) :
    CommandElabM (TSyntax `term) :=
  match order with
  | `(moduleRuleOrder| [$occurrences:moduleRuleOccurrence,*]) => do
      let values := (← occurrences.getElems.mapM occurrenceTerms).flatten
      `([$values,*])
  | `(moduleRuleOrder| from ($value:term)) => pure value
  | _ => throwUnsupportedSyntax

private def outputAlternative (clause : TSyntax `moduleOutputSchedule) :
    CommandElabM (TSyntax ``Parser.Term.matchAlt) :=
  match clause with
  | `(moduleOutputSchedule| | $rule:term => $order:moduleRuleOrder) => do
      let value ← orderTerm order
      `(matchAltExpr| | $rule => $value)
  | _ => throwUnsupportedSyntax

elab_rules : command
  | `(module_rule_schedules $derivedName:ident
      $parameters:moduleRuleScheduleParam* for $body:term with
      $childContracts:term implementing $contract:term where
      $outputKeyword:ident $outputs:moduleOutputSchedule*
      $stateKeyword:ident := $stateOrder:moduleRuleOrder) => do
    unless outputKeyword.getId == `output do
      throwErrorAt outputKeyword "expected `output` schedule section"
    unless stateKeyword.getId == `state do
      throwErrorAt stateKeyword "expected `state` schedule section"
    let params ← parameters.mapM parseParam
    let binders := params.map (·.binder)
    let arguments := params.map (·.argument)
    if outputs.isEmpty then
      throwErrorAt derivedName "module_rule_schedules requires an output schedule"
    let outputAlternatives ← outputs.mapM outputAlternative
    let stateValue ← orderTerm stateOrder
    let ordersName := mkIdentFrom derivedName (derivedName.getId.appendAfter "Orders")
    elabCommand <| ← `(
      private def $ordersName $binders:bracketedBinder* :
          Silean.Contracts.Cycle.Certification.Layer.ScheduleDerivation.RuleScheduleOrders
            ($body) ($childContracts) ($contract) := {
        «output» := fun $outputAlternatives:matchAlt*
        «state» := $stateValue }
    )
    elabCommand <| ← `(
      private noncomputable def $derivedName $binders:bracketedBinder* :
          Silean.Contracts.Cycle.Certification.Layer.ScheduleDerivation.DerivedRuleSchedules
            ($body) ($childContracts) ($contract) := by
        derive_rule_schedules ($ordersName $arguments:term*)
    )

end Silean.Authoring
