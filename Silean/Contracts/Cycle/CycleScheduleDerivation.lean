import Silean.Contracts.Cycle.CycleLayerSchedule
import Lean.Elab.Tactic

namespace Silean.Contracts.Cycle.Certification.Layer.ScheduleDerivation

open Silean

/-! # Deriving structural schedules

`derive_schedule` lets a module state only the intended order of child-rule
calls. During elaboration the tactic follows the fixed wiring graph, records
the exact earlier rule that supplies each read, and constructs the existing
proof-bearing `Schedule`. The kernel checks only those local certificates; it
does not repeat the graph search.
-/

/-- Explicit child-rule orders for every rule of one parent contract. -/
structure RuleScheduleOrders (body : ModuleBody)
    (childContracts : ChildCycleContracts body)
    (contract : ModuleCycleContract body.context.ports) where
  output : ∀ _name : contract.RuleName, List (RuleOccurrence body childContracts)
  state : List (RuleOccurrence body childContracts)

/-- All schedules for a contract together with their cross-schedule child-rule
coverage proof. -/
structure DerivedRuleSchedules (body : ModuleBody)
    (childContracts : ChildCycleContracts body)
    (contract : ModuleCycleContract body.context.ports) where
  schedules : RuleSchedules body childContracts contract
  coversChildren : schedules.CoversChildren

/-- One state-ready schedule that also calls every child rule. This is useful
for structural uniqueness proofs that do not have a parent cycle contract. -/
structure DerivedCompleteSchedule (body : ModuleBody)
    (childContracts : ChildCycleContracts body) where
  schedule : StateSchedule body childContracts
  coversAllRules : CoversAllRules body childContracts schedule.finalAvailability

def outputSchedulesFromCertificates
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {contract : ModuleCycleContract body.context.ports}
    (certificates : DependentList (fun name =>
      OutputSchedule body childContracts contract name) contract.ruleNames.values) :
    ∀ name, OutputSchedule body childContracts contract name :=
  fun name => certificates.get (contract.ruleNames.locate name)

theorem outputSchedulesFromCertificates_eq_get
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {contract : ModuleCycleContract body.context.ports}
    (certificates : DependentList (fun name =>
      OutputSchedule body childContracts contract name) contract.ruleNames.values)
    (name : contract.RuleName)
    (index : ListIndex name contract.ruleNames.values) :
    outputSchedulesFromCertificates certificates name = certificates.get index := by
  unfold outputSchedulesFromCertificates
  congr 1
  exact ListIndex.eq_of_nodup contract.ruleNames.nodup _ _

theorem outputSchedulesFromCertificates_mem_finalAvailability
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {contract : ModuleCycleContract body.context.ports}
    (certificates : DependentList (fun name =>
      OutputSchedule body childContracts contract name) contract.ruleNames.values)
    (name : contract.RuleName)
    (index : ListIndex name contract.ruleNames.values)
    (occurrence : RuleOccurrence body childContracts)
    (member : occurrence ∈ (certificates.get index).finalAvailability) :
    occurrence ∈
      (outputSchedulesFromCertificates certificates name).finalAvailability := by
  rw [outputSchedulesFromCertificates_eq_get certificates name index]
  exact member

theorem coversChildren_of_certificates
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {contract : ModuleCycleContract body.context.ports}
    (schedules : RuleSchedules body childContracts contract)
    (certificates : DependentList (fun child =>
      DependentList (fun rule => PLift
        (RuleOccurrence.mk child rule ∈ schedules.state.finalAvailability ∨
          ∃ name, RuleOccurrence.mk child rule ∈
            (schedules.output name).finalAvailability))
        (childContracts child).ruleNames.values)
      body.context.instancePorts.names.values) :
    schedules.CoversChildren := by
  intro child rule
  exact (certificates.get (body.context.instancePorts.names.locate child) |>.get
    ((childContracts child).ruleNames.locate rule)).down

/-- Compact numeric identity for a dependent child-rule occurrence. -/
def occurrenceKey
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (occurrence : RuleOccurrence body childContracts) : Nat × Nat :=
  ((body.context.instancePorts.names.ordinal occurrence.child).val,
    ((childContracts occurrence.child).ruleNames.ordinal occurrence.rule).val)

private theorem key_mem_of_occurrence_mem
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {occurrence : RuleOccurrence body childContracts}
    {available : Availability body childContracts}
    (member : occurrence ∈ available) :
    occurrenceKey occurrence ∈ available.map occurrenceKey := by
  exact List.mem_map.mpr ⟨occurrence, member, rfl⟩

/-- Turn one availability proof per declared read into the universal premise
required by `Schedule.call`.  The tactic constructs this dependent list one
read at a time, keeping kernel reduction local to a single wiring endpoint. -/
theorem readsAvailable_of_certificates
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (available : Availability body childContracts)
    (occurrence : RuleOccurrence body childContracts)
    (certificates : DependentList (fun input => PLift
      (sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))) occurrence.reads) :
    ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input) := by
  letI : DecidableEq
      (body.context.instancePorts.ports occurrence.child).inputs.Label :=
    (body.context.instancePorts.ports occurrence.child).inputs.labels.decidableEq
  intro input member
  exact (certificates.get (ListIndex.ofMem member)).down

def moduleInputReadyBool
    {body : ModuleBody}
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (decideInput : ∀ input, Decidable (inputAvailable input))
    (input : body.context.ports.inputs.Label) : Bool :=
  @decide (inputAvailable input) (decideInput input)

theorem moduleInputAvailable_of_bool_eq_true
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (decideInput : ∀ input, Decidable (inputAvailable input))
    (available : Availability body childContracts)
    (input : body.context.ports.inputs.Label)
    (ready : moduleInputReadyBool inputAvailable decideInput input = true) :
    sourceAvailable inputAvailable available (.moduleInput input) :=
  @of_decide_eq_true _ (decideInput input) ready

theorem enumerationValue_mem
    {α : Type} (enumeration : Enumeration α) (value : α) :
    value ∈ enumeration.values :=
  ListIndex.get_eq (enumeration.locate value) ▸ List.get_mem _ _

theorem signalLabel_mem_allSelection (signals : SignalMap)
    (label : signals.Label) : label ∈ signals.allSelection.labels := by
  rw [SignalMap.allSelection_labels]
  exact enumerationValue_mem signals.labels label

/-- If a child contract has exactly one output rule, every child output is
written by that rule. This supports symbolically sized output families without
enumerating their labels during elaboration. -/
theorem output_written_by_only_rule
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (child : body.context.instancePorts.Name)
    (rule : (childContracts child).RuleName)
    (only : (childContracts child).ruleNames.values = [rule])
    (output : (body.context.instancePorts.ports child).outputs.Label) :
    output ∈ (RuleOccurrence.mk child rule :
      RuleOccurrence body childContracts).writes := by
  have written := (childContracts child).output_is_written output
  rw [ModuleCycleContract.writtenOutputs, only] at written
  simpa [RuleOccurrence.writes] using written

/-- Availability through a decidable wiring branch follows by checking both
branches. Generated wiring for symbolic `Fin` ranges commonly has this form. -/
theorem sourceAvailable_decidable_rec
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {available : Availability body childContracts}
    {signalType : SignalType} {condition : Prop}
    (whenFalse : ¬condition → SignalSource body.context.ports
      body.context.instancePorts signalType)
    (whenTrue : condition → SignalSource body.context.ports
      body.context.instancePorts signalType)
    (decision : Decidable condition)
    (falseAvailable : ∀ proof, sourceAvailable inputAvailable available
      (whenFalse proof))
    (trueAvailable : ∀ proof, sourceAvailable inputAvailable available
      (whenTrue proof)) :
    sourceAvailable inputAvailable available
      (@Decidable.rec condition
        (fun _ => SignalSource body.context.ports
          body.context.instancePorts signalType)
        whenFalse whenTrue decision) := by
  cases decision with
  | isFalse proof => exact falseAvailable proof
  | isTrue proof => exact trueAvailable proof

/-- Compact freshness check for a scheduled occurrence. -/
def freshBool
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (available : Availability body childContracts)
    (occurrence : RuleOccurrence body childContracts) : Bool :=
  decide (occurrenceKey occurrence ∉ available.map occurrenceKey)

/-- The compact freshness check supplies the proposition required by
`Schedule.call`. -/
theorem fresh_of_bool_eq_true
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (available : Availability body childContracts)
    (occurrence : RuleOccurrence body childContracts)
    (fresh : freshBool available occurrence = true) :
    occurrence ∉ available := by
  have keyFresh : occurrenceKey occurrence ∉ available.map occurrenceKey :=
    of_decide_eq_true fresh
  exact fun member => keyFresh (key_mem_of_occurrence_mem member)

def childFreshBool
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (available : Availability body childContracts)
    (occurrence : RuleOccurrence body childContracts) : Bool :=
  letI := body.context.instancePorts.names.decidableEq
  decide (occurrence.child ∉ available.map RuleOccurrence.child)

theorem child_fresh_of_bool_eq_true
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (available : Availability body childContracts)
    (occurrence : RuleOccurrence body childContracts)
    (fresh : childFreshBool available occurrence = true) :
    occurrence.child ∉ available.map RuleOccurrence.child := by
  letI := body.context.instancePorts.names.decidableEq
  have fresh' : decide
      (occurrence.child ∉ available.map RuleOccurrence.child) = true := by
    simpa [childFreshBool] using fresh
  exact of_decide_eq_true fresh'

theorem fresh_of_child_bool_eq_true
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (available : Availability body childContracts)
    (occurrence : RuleOccurrence body childContracts)
    (fresh : childFreshBool available occurrence = true) :
    occurrence ∉ available := by
  have childFresh := child_fresh_of_bool_eq_true available occurrence fresh
  intro member
  exact childFresh (List.mem_map.mpr ⟨occurrence, member, rfl⟩)

def childrenDifferentBool
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (left right : RuleOccurrence body childContracts) : Bool :=
  letI := body.context.instancePorts.names.decidableEq
  decide (left.child ≠ right.child)

theorem children_different_of_bool_eq_true
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (left right : RuleOccurrence body childContracts)
    (different : childrenDifferentBool left right = true) :
    left.child ≠ right.child := by
  letI := body.context.instancePorts.names.decidableEq
  apply of_decide_eq_true
  simpa [childrenDifferentBool] using different

theorem fresh_after_family_of_child_disjoint
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    (initial : Availability body childContracts)
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence body childContracts)
    (injective : Function.Injective occurrence)
    (fresh : ∀ index, occurrence index ∉ initial)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable initial
        (body.wiring.instanceInput (occurrence index).child input))
    (candidate : RuleOccurrence body childContracts)
    (oldChildrenDifferent : candidate.child ∉ initial.map RuleOccurrence.child)
    (familyChildrenDifferent : ∀ index,
      candidate.child ≠ (occurrence index).child) :
    candidate ∉ (Schedule.callFamilyAfter initial indices occurrence injective
      fresh readsAvailable).finalAvailability := by
  intro member
  rw [Schedule.mem_finalAvailability_callFamilyAfter_iff] at member
  rcases member with old | ⟨index, equal⟩
  · exact oldChildrenDifferent (List.mem_map.mpr ⟨candidate, old, rfl⟩)
  · exact familyChildrenDifferent index (congrArg RuleOccurrence.child equal)

theorem fresh_after_family
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    (initial : Availability body childContracts)
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence body childContracts)
    (injective : Function.Injective occurrence)
    (fresh : ∀ index, occurrence index ∉ initial)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable initial
        (body.wiring.instanceInput (occurrence index).child input))
    (candidate : RuleOccurrence body childContracts)
    (oldFresh : candidate ∉ initial)
    (familyChildrenDifferent : ∀ index,
      candidate.child ≠ (occurrence index).child) :
    candidate ∉ (Schedule.callFamilyAfter initial indices occurrence injective
      fresh readsAvailable).finalAvailability := by
  intro member
  rw [Schedule.mem_finalAvailability_callFamilyAfter_iff] at member
  rcases member with old | ⟨index, equal⟩
  · exact oldFresh old
  · exact familyChildrenDifferent index (congrArg RuleOccurrence.child equal)

theorem fresh_cons_of_child_disjoint
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (candidate head : RuleOccurrence body childContracts)
    (tail : Availability body childContracts)
    (different : candidate.child ≠ head.child)
    (freshTail : candidate ∉ tail) :
    candidate ∉ head :: tail := by
  intro member
  rcases List.mem_cons.mp member with equal | inTail
  · exact different (congrArg RuleOccurrence.child equal)
  · exact freshTail inTail

/-- Direct certificates for each required parent output establish the output
boundary without searching the scheduled rules again. -/
theorem boundaryReady_of_certificates
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (outputs : List body.context.ports.outputs.Label)
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (available : Availability body childContracts)
    (certificates : DependentList (fun output => PLift
      (sourceAvailable inputAvailable available
        (body.wiring.moduleOutput output))) outputs) :
    BoundaryReady body childContracts outputs inputAvailable available := by
  letI : DecidableEq body.context.ports.outputs.Label :=
    body.context.ports.outputs.labels.decidableEq
  intro output member
  exact (certificates.get (ListIndex.ofMem member)).down

/-- Direct certificates for every input used by every child state rule
establish the state boundary without re-running an availability search. -/
theorem stateBoundaryReady_of_certificates
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (available : Availability body childContracts)
    (certificates : DependentList (fun child =>
      DependentList (fun input => PLift
        (sourceAvailable (fun _ => True) available
          (body.wiring.instanceInput child input)))
        (childContracts child).stateRule.readsInputs.labels)
      body.context.instancePorts.names.values) :
    ChildrenStateInputsReady body childContracts available := by
  intro child input member
  let inputs := certificates.get (body.context.instancePorts.names.locate child)
  letI : DecidableEq
      (body.context.instancePorts.ports child).inputs.Label :=
    (body.context.instancePorts.ports child).inputs.labels.decidableEq
  exact (inputs.get (ListIndex.ofMem member)).down

end Silean.Contracts.Cycle.Certification.Layer.ScheduleDerivation

namespace Silean.Contracts.Cycle.Certification.Layer

open Lean Elab Tactic Meta

private inductive FinishKind where
  | outputs (labels : Expr)
  | state

private inductive OrderStep where
  | call (occurrence : Expr)
  | family (indexType indices occurrence : Expr)

private structure ConcreteProvider where
  occurrence : Expr
  member : Expr

private structure FamilyProvider where
  indexType : Expr
  initial : Expr
  indices : Expr
  occurrence : Expr
  injective : Expr
  fresh : Expr
  reads : Expr
  schedule : Expr
  member : Expr

private def proveBySimp (type : Expr) (description : MessageData) : MetaM Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let (remaining, _) ← Lean.Elab.runTactic goal.mvarId!
    (← `(tactic| first | simp | assumption | (intro member; cases member) | rfl))
  unless remaining.isEmpty do
    let details ← remaining.mapM fun goal => goal.withContext do
      pure m!"{indentExpr (← goal.getType)}"
    throwError "`derive_schedule` could not prove {description}:{indentD details}"
  instantiateMVars goal

private def proveOutputMembershipBySimp
    (type : Expr) : MetaM Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let (remaining, _) ← Lean.Elab.runTactic goal.mvarId!
    (← `(tactic| simp [RuleOccurrence.writes]))
  for current in remaining do
    current.withContext do
      let target ← current.getType
      let arguments := target.getAppArgs
      unless arguments.size >= 2 do
        throwError "public child-rule facts do not establish output membership"
      let listMem := target.getAppFn.constName? == some ``List.Mem
      let valuesArgument := if listMem then
        arguments.back!
      else
        arguments[arguments.size - 2]!
      let output := if listMem then
        arguments[arguments.size - 2]!
      else
        arguments.back!
      let values ← withTransparency .reducible <|
        whnf valuesArgument
      let (constructor, listArguments) := values.getAppFnArgs
      unless constructor == ``List.cons && listArguments.size == 3 do
        throwError "public child-rule output list is not a singleton"
      let head := listArguments[1]!
      let tail ← withTransparency .reducible <| whnf listArguments[2]!
      unless tail.getAppFn.constName? == some ``List.nil &&
          (← withTransparency .all <| isDefEq output head) do
        throwError "public child-rule output singleton does not match"
      current.assign <| mkAppN (mkConst ``List.mem_cons_self [.zero])
        #[listArguments[0]!, head, tail]
  let proof ← instantiateMVars goal
  if proof.hasMVar then
    throwError "public child-rule output proof has unresolved metavariables"
  unless ← withTransparency .all <| isDefEq (← inferType proof) type do
    throwError "public child-rule output proof has the wrong type"
  pure proof

private def proveOccurrenceFamilyInjective (type : Expr)
    (description : MessageData) : MetaM Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let (afterIntro, _) ← Lean.Elab.runTactic goal.mvarId!
    (← `(tactic| intro left right equal))
  let mut afterHave := []
  for current in afterIntro do
    let (next, _) ← Lean.Elab.runTactic current
      (← `(tactic|
        have childEqual := congrArg RuleOccurrence.child equal))
    afterHave := afterHave ++ next
  let mut remaining := []
  for current in afterHave do
    let (next, _) ← Lean.Elab.runTactic current
      (← `(tactic| injection childEqual <;> simp_all))
    remaining := remaining ++ next
  unless remaining.isEmpty do
    throwError "`derive_schedule` could not prove {description}:{indentExpr type}"
  instantiateMVars goal

private def proveChildDifferent (left right : Expr)
    (description : MessageData) : MetaM Expr := do
  let leftChild ← mkAppM ``RuleOccurrence.child #[left]
  let rightChild ← mkAppM ``RuleOccurrence.child #[right]
  let equality ← mkAppM ``Eq #[leftChild, rightChild]
  let type ← mkAppM ``Not #[equality]
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let (afterIntro, _) ← Lean.Elab.runTactic goal.mvarId!
    (← `(tactic| intro equal))
  let mut remaining := []
  for current in afterIntro do
    let (next, _) ← Lean.Elab.runTactic current (← `(tactic| cases equal))
    remaining := remaining ++ next
  unless remaining.isEmpty do
    throwError "`derive_schedule` could not prove {description}:{indentExpr type}"
  instantiateMVars goal

private def casesOnWiringParameters (type : Expr) :
    MetaM (Expr × List MVarId) := do
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let mut goals := [goal.mvarId!]
  for userName in [`splitter, `input] do
    let mut nextGoals := []
    for current in goals do
      let candidates ← current.withContext do
        let localContext ← getLCtx
        pure (localContext.getFVarIds.toList.filter fun candidate =>
          match localContext.find? candidate with
          | some declaration => declaration.userName == userName
          | none => false)
      let mut alternatives := [current]
      for candidate in candidates do
        let mut splitGoals := []
        for alternative in alternatives do
          let split? ← try
            pure (some (← alternative.cases candidate))
          catch _ => pure none
          match split? with
          | some cases =>
              splitGoals := splitGoals ++ cases.toList.map (fun result => result.mvarId)
          | none => splitGoals := splitGoals ++ [alternative]
        alternatives := splitGoals
      nextGoals := nextGoals ++ alternatives
    goals := nextGoals
  pure (goal, goals)

private def casesOnStateBoundaryInput (type : Expr) :
    MetaM (Expr × List MVarId) := do
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let typeArguments := type.getAppArgs
  if typeArguments.isEmpty then return (goal, [goal.mvarId!])
  let sourceArguments := typeArguments.back!.getAppArgs
  if sourceArguments.isEmpty then return (goal, [goal.mvarId!])
  let input := sourceArguments.back!
  unless input.isFVar do return (goal, [goal.mvarId!])
  let cases? ← try
    pure (some (← goal.mvarId!.cases input.fvarId!))
  catch _ => pure none
  match cases? with
  | some cases => pure (goal, cases.toList.map (fun result => result.mvarId))
  | none => pure (goal, [goal.mvarId!])

/-- Construct a proof-bearing output or state schedule from an explicit order
of child-rule occurrences. The expected schedule type determines which final
boundary condition is checked. -/
syntax (name := deriveSchedule) "derive_schedule" term : tactic
syntax (name := deriveRuleSchedules) "derive_rule_schedules" term : tactic
syntax (name := deriveCompleteSchedule) "derive_complete_schedule" term : tactic

private partial def exprList (value : Expr) : MetaM (List Expr) := do
  let value ← withTransparency .all <| whnf value
  let (constructor, arguments) := value.getAppFnArgs
  if constructor == ``List.nil then
    pure []
  else if constructor == ``List.cons && arguments.size == 3 then
    return arguments[1]! :: (← exprList arguments[2]!)
  else
    throwError "`derive_schedule` needs a concrete ordered list, got:{indentExpr value}"

private partial def orderSteps (value : Expr) : MetaM (List OrderStep) := do
  let value ← withTransparency .all <| whnf value
  let (constructor, arguments) := value.getAppFnArgs
  if constructor == ``List.nil then
    pure []
  else if constructor == ``List.cons && arguments.size == 3 then
    return .call arguments[1]! :: (← orderSteps arguments[2]!)
  else if constructor == ``List.append && arguments.size == 3 then
    return (← orderSteps arguments[1]!) ++ (← orderSteps arguments[2]!)
  else if constructor == ``List.map && arguments.size == 4 then
    let occurrence := arguments[2]!
    let values := arguments[3]!
    let (valuesConstructor, valuesArguments) := values.getAppFnArgs
    unless valuesConstructor == ``Enumeration.values && valuesArguments.size >= 1 do
      throwError "`derive_schedule` only supports mapped schedule families over an `Enumeration` ({valuesConstructor}, {valuesArguments.size} arguments), got:{indentExpr value}"
    pure [.family arguments[0]! valuesArguments.back! occurrence]
  else
    throwError "`derive_schedule` needs calls and enumerated call families, got:{indentExpr value}"

private partial def membershipAt (values : Expr) (index : Nat) : MetaM Expr := do
  let reduced ← withTransparency .all <| whnf values
  let (constructor, arguments) := reduced.getAppFnArgs
  unless constructor == ``List.cons && arguments.size == 3 do
    throwError "internal `derive_schedule` error: invalid membership index {index}"
  let head := arguments[1]!
  let tail := arguments[2]!
  if index == 0 then
    pure <| mkAppN (mkConst ``List.mem_cons_self [.zero])
      #[arguments[0]!, head, tail]
  else
    let member ← membershipAt tail (index - 1)
    mkAppM ``List.mem_cons_of_mem #[head, member]

private partial def proveFreshFromAvailability (candidate available : Expr)
    (families : List FamilyProvider) (description : MessageData) : MetaM Expr := do
  let entries? ← try pure (some (← exprList available)) catch _ => pure none
  if let some entries := entries? then
    let occurrenceType ← inferType candidate
    let mut tail := mkApp (mkConst ``List.nil [.zero]) occurrenceType
    let mut proof ← proveBySimp (← mkAppM ``Not
      #[← mkAppM ``List.Mem #[candidate, tail]]) description
    for entry in entries.reverse do
      let different ← proveChildDifferent candidate entry description
      proof ← mkAppM ``ScheduleDerivation.fresh_cons_of_child_disjoint
        #[candidate, entry, tail, different, proof]
      tail ← mkAppM ``List.cons #[entry, tail]
    unless ← withTransparency .all <| isDefEq tail available do
      throwError "availability reconstruction failed"
    return proof
  let mut precedingCalls : List Expr := []
  let mut familyTail := available
  let mut peeling := true
  while peeling do
    let (tailName, tailArguments) := familyTail.getAppFnArgs
    if tailName == ``List.cons && tailArguments.size == 3 then
      precedingCalls := precedingCalls ++ [tailArguments[1]!]
      familyTail := tailArguments[2]!
    else
      peeling := false
  for family in families do
    let familyFinal ← mkAppM ``Schedule.finalAvailability #[family.schedule]
    if ← withTransparency .all <| isDefEq familyFinal familyTail then
      let oldFresh ← proveFreshFromAvailability candidate family.initial
        families description
      let familyDifferent ← withLocalDeclD `index family.indexType fun index => do
        let called := mkApp family.occurrence index
        let proof ← proveChildDifferent candidate called description
        mkLambdaFVars #[index] proof
      let mut proof ← mkAppM ``ScheduleDerivation.fresh_after_family
        #[family.initial, family.indices, family.occurrence, family.injective,
          family.fresh, family.reads, candidate, oldFresh, familyDifferent]
      let mut tail := familyTail
      for head in precedingCalls.reverse do
        let different ← proveChildDifferent candidate head description
        proof ← mkAppM ``ScheduleDerivation.fresh_cons_of_child_disjoint
          #[candidate, head, tail, different, proof]
        tail ← mkAppM ``List.cons #[head, tail]
      return proof
  throwError "`derive_schedule` could not prove {description}"

private partial def listIndexAt (values : Expr) (index : Nat) : MetaM Expr := do
  let reduced ← withTransparency .all <| whnf values
  let (constructor, arguments) := reduced.getAppFnArgs
  unless constructor == ``List.cons && arguments.size == 3 do
    throwError "internal `derive_schedule` error: invalid list-index position {index}"
  let elementType := arguments[0]!
  let head := arguments[1]!
  let tail := arguments[2]!
  if index == 0 then
    pure <| mkAppN (mkConst ``ListIndex.head [.zero])
      #[elementType, head, tail]
  else
    let rest ← listIndexAt tail (index - 1)
    pure <| mkAppN (mkConst ``ListIndex.tail [.zero])
      #[elementType, head, rest]

private def sameExpr (left right : Expr) : MetaM Bool :=
  if left == right then
    pure true
  else
    withTransparency .all <| isDefEq left right

private def occurrenceProjection (projection : Name) (occurrence : Expr) : MetaM Expr := do
  let occurrenceType ← withTransparency .reducible <| whnf (← inferType occurrence)
  let arguments := occurrenceType.getAppArgs
  unless arguments.size == 2 do
    throwError "internal `derive_schedule` error: malformed rule occurrence:{indentExpr occurrenceType}"
  pure (mkAppN (mkConst projection) #[arguments[0]!, arguments[1]!, occurrence])

private def occurrenceChild (occurrence : Expr) : MetaM Expr :=
  occurrenceProjection ``RuleOccurrence.child occurrence

private partial def normalizeFinalAvailability (available : Expr) : MetaM Expr := do
  let (name, arguments) := available.getAppFnArgs
  unless name == ``Schedule.finalAvailability && !arguments.isEmpty do
    return available
  let schedule := arguments.back!
  let (scheduleName, scheduleArguments) := schedule.getAppFnArgs
  if scheduleName == ``Schedule.call && !scheduleArguments.isEmpty then
    return ← normalizeFinalAvailability (← mkAppM ``Schedule.finalAvailability
      #[scheduleArguments.back!])
  if scheduleName == ``Schedule.append && !scheduleArguments.isEmpty then
    return ← normalizeFinalAvailability (← mkAppM ``Schedule.finalAvailability
      #[scheduleArguments.back!])
  if scheduleName == ``Schedule.done && scheduleArguments.size >= 2 then
    return scheduleArguments[scheduleArguments.size - 2]!
  return available

private def familyProviderFromAvailability? (available : Expr) :
    MetaM (Option FamilyProvider) := do
  let (finalName, finalArguments) := available.getAppFnArgs
  unless finalName == ``Schedule.finalAvailability && !finalArguments.isEmpty do
    return none
  let schedule := finalArguments.back!
  let (scheduleName, scheduleArguments) := schedule.getAppFnArgs
  unless scheduleName == ``Schedule.callFamilyAfter && scheduleArguments.size >= 7 do
    return none
  let initial := scheduleArguments[scheduleArguments.size - 7]!
  let indices := scheduleArguments[scheduleArguments.size - 5]!
  let occurrence := scheduleArguments[scheduleArguments.size - 4]!
  let injective := scheduleArguments[scheduleArguments.size - 3]!
  let fresh := scheduleArguments[scheduleArguments.size - 2]!
  let reads := scheduleArguments.back!
  let indicesType ← withTransparency .reducible <| whnf (← inferType indices)
  let indexType := indicesType.getAppArgs[0]!
  let finished ← mkAppM ``Schedule.finished #[schedule]
  let familyFacts := mkProj ``And 1 finished
  let includesFamily := mkProj ``And 0 familyFacts
  let member ← withLocalDeclD `index indexType fun index =>
    mkLambdaFVars #[index] (mkApp includesFamily index)
  pure (some ⟨indexType, initial, indices, occurrence, injective, fresh,
    reads, schedule, member⟩)

private partial def providersFromAvailability (available : Expr) :
    MetaM (List ConcreteProvider × List FamilyProvider) := do
  let available ← normalizeFinalAvailability available
  if let some family ← familyProviderFromAvailability? available then
    let (oldConcrete, oldFamilies) ← providersFromAvailability family.initial
    let finished ← mkAppM ``Schedule.finished #[family.schedule]
    let includesOld := mkProj ``And 0 finished
    let mut concrete : List ConcreteProvider := []
    for provider in oldConcrete do
      concrete := concrete ++ [⟨provider.occurrence,
        mkApp2 includesOld provider.occurrence provider.member⟩]
    let mut families : List FamilyProvider := []
    for provider in oldFamilies do
      let member ← withLocalDeclD `index provider.indexType fun index => do
        let called := mkApp provider.occurrence index
        let oldMember := mkApp provider.member index
        mkLambdaFVars #[index] (mkApp2 includesOld called oldMember)
      families := families ++ [{ provider with member := member }]
    return (concrete, families ++ [family])
  let reduced ← withTransparency .all <| whnf available
  let (constructor, arguments) := reduced.getAppFnArgs
  if constructor == ``List.nil then
    return ([], [])
  if constructor == ``List.cons && arguments.size == 3 then
    let head := arguments[1]!
    let tail := arguments[2]!
    let (oldConcrete, oldFamilies) ← providersFromAvailability tail
    let headMember := mkAppN (mkConst ``List.mem_cons_self [.zero])
      #[arguments[0]!, head, tail]
    let mut concrete : List ConcreteProvider := [⟨head, headMember⟩]
    for provider in oldConcrete do
      let member ← mkAppM ``List.mem_cons_of_mem #[head, provider.member]
      concrete := concrete ++ [⟨provider.occurrence, member⟩]
    let mut families : List FamilyProvider := []
    for provider in oldFamilies do
      let member ← withLocalDeclD `index provider.indexType fun index => do
        let oldMember := mkApp provider.member index
        let lifted ← mkAppM ``List.mem_cons_of_mem #[head, oldMember]
        mkLambdaFVars #[index] lifted
      families := families ++ [{ provider with member := member }]
    return (concrete, families)
  throwError "internal `derive_rule_schedules` error: cannot inspect final availability:{indentExpr available}"

private def findProviderMembership (occurrence available : Expr) : MetaM Expr := do
  let (concrete, families) ← providersFromAvailability available
  for provider in concrete do
    if ← sameExpr occurrence provider.occurrence then
      return (← instantiateMVars provider.member)
  for family in families do
    let index ← mkFreshExprMVar (some family.indexType)
    if ← sameExpr occurrence (mkApp family.occurrence index) then
      let index ← instantiateMVars index
      unless index.hasMVar do
        return (← instantiateMVars (mkApp family.member index))
  throwError "scheduled rules do not contain child rule:{indentExpr occurrence}"

private def mkInputDecidableEq (body : Expr) : MetaM Expr := do
  let context ← mkAppM ``ModuleBody.context #[body]
  let ports ← mkAppM ``EndpointContext.ports #[context]
  let inputs ← mkAppM ``ModulePorts.inputs #[ports]
  let labels ← mkAppM ``EnumeratedMap.keys #[inputs]
  mkAppM ``Enumeration.decidableEq #[labels]

private def mkDecideInput (inputAvailable inputDecidableEq : Expr) : MetaM Expr := do
  let inputType := (← whnf (← inferType inputAvailable)).bindingDomain!
  let decidableEqType ← mkAppM ``DecidableEq #[inputType]
  withLocalDecl `inputDecidableEq .instImplicit decidableEqType fun localInstance => do
    let decisionFunction ← withLocalDeclD `input inputType fun input => do
      let property := mkApp inputAvailable input
      let decision ← synthInstance (mkApp (mkConst ``Decidable) property)
      mkLambdaFVars #[input] decision
    let decisionFunction ← instantiateMVars decisionFunction
    let abstracted ← mkLambdaFVars #[localInstance] decisionFunction
    whnf (mkApp abstracted inputDecidableEq)

private def mkSourceAvailableExpr
    (body childContracts inputAvailable available source : Expr) : MetaM Expr := do
  let signalType := (← withTransparency .reducible <| whnf (← inferType source))
    |>.getAppArgs.back!
  pure <| mkAppN (mkConst ``sourceAvailable)
    #[body, childContracts, signalType, inputAvailable, available, source]

private partial def proveSourceAvailable
    (body childContracts inputAvailable decideInput available source : Expr)
    (concreteProviders : List ConcreteProvider)
    (familyProviders : List FamilyProvider)
    (location : MessageData) : MetaM Expr := do
  let reduced ← withTransparency .all <| whnf source
  let (constructor, arguments) := reduced.getAppFnArgs
  if constructor == ``SignalSource.moduleInput then
    let input := arguments.back!
    if inputAvailable.isLambda then
      let required := inputAvailable.bindingBody!.instantiate1 input
      let requiredArguments := required.getAppArgs
      if requiredArguments.size >= 2 then
        let labels := requiredArguments[requiredArguments.size - 2]!
        try
          let entries ← exprList labels
          for (entry, index) in entries.zipIdx do
            if ← sameExpr input entry then
              return ← membershipAt labels index
        catch _ => pure ()
        try
          let reducedLabels ← withTransparency .all <| reduceAll labels
          let (labelsName, labelsArguments) := reducedLabels.getAppFnArgs
          if labelsName == ``Enumeration.values && !labelsArguments.isEmpty then
            let enumeration := labelsArguments.back!
            let proof ← mkAppM ``ScheduleDerivation.enumerationValue_mem
              #[enumeration, input]
            unless ← withTransparency .all <|
                isDefEq (← inferType proof) required do
              throwError "enumeration membership has the wrong type"
            return proof
          if labelsName == ``SignalSelection.labels &&
              !labelsArguments.isEmpty then
            let selection := labelsArguments.back!
            let (selectionName, selectionArguments) := selection.getAppFnArgs
            if selectionName == ``SignalMap.selectionFrom &&
                selectionArguments.size >= 2 then
              let signals := selectionArguments[selectionArguments.size - 2]!
              let proof ← mkAppM
                ``ScheduleDerivation.signalLabel_mem_allSelection
                #[signals, input]
              unless ← withTransparency .all <|
                  isDefEq (← inferType proof) required do
                throwError "all-selection membership has the wrong type"
              return proof
        catch _ => pure ()
    let check := mkAppN (mkConst ``ScheduleDerivation.moduleInputReadyBool)
      #[body, inputAvailable, decideInput, input]
    unless ← withTransparency .all <| isDefEq check (mkConst ``true) do
      try
        return ← proveBySimp (mkApp inputAvailable input)
          m!"availability of parent input at {location}"
      catch _ =>
        try
          let required := mkApp inputAvailable input
          let reducedRequired ← withTransparency .all <| reduceAll required
          let proof ← proveBySimp reducedRequired
            m!"normalized availability of parent input at {location}"
          unless ← withTransparency .all <|
              isDefEq (← inferType proof) required do
            throwError "normalized input-availability proof has the wrong type"
          return proof
        catch _ =>
          throwError "invalid structural schedule at {location}: uses an unavailable parent input:{indentExpr input}\nrequired by:{indentExpr inputAvailable}"
    let checkProof ← mkEqRefl check
    pure <| mkAppN
      (mkConst ``ScheduleDerivation.moduleInputAvailable_of_bool_eq_true)
      #[body, childContracts, inputAvailable, decideInput, available, input,
        checkProof]
  else if constructor == ``SignalSource.instanceOutput && arguments.size >= 4 then
    let sourceChild := arguments[arguments.size - 2]!
    let sourceOutput := arguments.back!
    for providerInfo in concreteProviders do
      let provider := providerInfo.occurrence
      let providerChild ← occurrenceChild provider
      if ← sameExpr providerChild sourceChild then
        let writes ← mkAppM ``RuleOccurrence.writes #[provider]
        let providerRule ← mkAppM ``RuleOccurrence.rule #[provider]
        let writtenOutputs? ← try
          pure (some (← exprList writes))
        catch _ => pure none
        let mut writtenProof? : Option Expr := none
        if let some writtenOutputs := writtenOutputs? then
          for (written, writtenIndex) in writtenOutputs.zipIdx do
            if ← sameExpr written sourceOutput then
              writtenProof? := some (← membershipAt writes writtenIndex)
        if writtenProof?.isNone then
          let childContract := mkApp childContracts sourceChild
          let names ← mkAppM ``ModuleCycleContract.ruleNames #[childContract]
          let ruleType := (← whnf (← inferType names)).getAppArgs[0]!
          let ruleValues := mkAppN (mkConst ``Enumeration.values [.zero])
            #[ruleType, names]
          let rules? ← try
            pure (some (← exprList ruleValues))
          catch _ => pure none
          if let some [onlyRule] := rules? then
            if ← sameExpr onlyRule providerRule then
              let onlyProof ← mkEqRefl ruleValues
              writtenProof? := some (mkAppN
                (mkConst ``ScheduleDerivation.output_written_by_only_rule)
                #[body, childContracts, sourceChild, providerRule, onlyProof,
                  sourceOutput])
        if writtenProof?.isNone then
          let membership ← mkAppM ``List.Mem #[sourceOutput, writes]
          if let some proof ← observing? (proveOutputMembershipBySimp membership) then
            writtenProof? := some proof
        if let some written := writtenProof? then
          return mkAppN (mkConst ``sourceAvailable_of_instanceOutput)
            #[body, childContracts, inputAvailable, available, sourceChild,
              providerRule, sourceOutput, providerInfo.member, written]
    for family in familyProviders do
      let index ← mkFreshExprMVar (some family.indexType)
      let provider := mkApp family.occurrence index
      let providerChild ← occurrenceChild provider
      if ← sameExpr providerChild sourceChild then
        let index ← instantiateMVars index
        unless index.hasMVar do
          let provider := mkApp family.occurrence index
          let writes ← mkAppM ``RuleOccurrence.writes #[provider]
          let providerRule ← mkAppM ``RuleOccurrence.rule #[provider]
          let writtenOutputs? ← try
            pure (some (← exprList writes))
          catch _ => pure none
          let mut writtenProof? : Option Expr := none
          if let some writtenOutputs := writtenOutputs? then
            for (written, writtenIndex) in writtenOutputs.zipIdx do
              if ← sameExpr written sourceOutput then
                writtenProof? := some (← membershipAt writes writtenIndex)
          if writtenProof?.isNone then
            let childContract := mkApp childContracts sourceChild
            let names ← mkAppM ``ModuleCycleContract.ruleNames #[childContract]
            let ruleType := (← whnf (← inferType names)).getAppArgs[0]!
            let ruleValues := mkAppN (mkConst ``Enumeration.values [.zero])
              #[ruleType, names]
            let rules? ← try
              pure (some (← exprList ruleValues))
            catch _ => pure none
            if let some [onlyRule] := rules? then
              if ← sameExpr onlyRule providerRule then
                let onlyProof ← mkEqRefl ruleValues
                writtenProof? := some (mkAppN
                  (mkConst ``ScheduleDerivation.output_written_by_only_rule)
                  #[body, childContracts, sourceChild, providerRule, onlyProof,
                    sourceOutput])
          if writtenProof?.isNone then
            let membership ← mkAppM ``List.Mem #[sourceOutput, writes]
            if let some proof ← observing? (proveOutputMembershipBySimp membership) then
              writtenProof? := some proof
          if let some written := writtenProof? then
            let called := mkApp family.member index
            let proof := mkAppN (mkConst ``sourceAvailable_of_instanceOutput)
              #[body, childContracts, inputAvailable, available, sourceChild,
                providerRule, sourceOutput, called, written]
            let proof ← instantiateMVars proof
            try
              discard <| inferType proof
            catch error =>
              throwError "invalid family availability proof at {location}: {error.toMessageData}{indentExpr proof}"
            return proof
    throwError
      "invalid structural schedule at {location}: uses a child output that no earlier rule has produced ({familyProviders.length} available families):{indentExpr reduced}"
  else if constructor == ``Decidable.rec && arguments.size == 5 then
    let whenFalse := arguments[2]!
    let whenTrue := arguments[3]!
    let decision := arguments[4]!
    let sourceType ← withTransparency .all <| whnf (← inferType reduced)
    let signalType := sourceType.getAppArgs.back!
    let falseType := (← withTransparency .all <| whnf (← inferType whenFalse)).bindingDomain!
    let falseAvailable ← withLocalDeclD `notCondition falseType fun proof => do
      let branchSource := mkApp whenFalse proof
      let branchProof ← proveSourceAvailable body childContracts inputAvailable
        decideInput available branchSource concreteProviders familyProviders location
      mkLambdaFVars #[proof] branchProof
    let trueType := (← withTransparency .all <| whnf (← inferType whenTrue)).bindingDomain!
    let trueAvailable ← withLocalDeclD `condition trueType fun proof => do
      let branchSource := mkApp whenTrue proof
      let branchProof ← proveSourceAvailable body childContracts inputAvailable
        decideInput available branchSource concreteProviders familyProviders location
      mkLambdaFVars #[proof] branchProof
    pure <| mkAppN (mkConst ``ScheduleDerivation.sourceAvailable_decidable_rec)
      #[body, childContracts, inputAvailable, available, signalType,
        arguments[0]!, whenFalse, whenTrue, decision, falseAvailable,
        trueAvailable]
  else if constructor == ``Eq.rec && arguments.size == 6 then
    let type := arguments[0]!
    let sourceAt := arguments[1]!
    let sourceMotive := arguments[2]!
    let innerSource := arguments[3]!
    let to := arguments[4]!
    let equality := arguments[5]!
    let innerProof ← proveSourceAvailable body childContracts inputAvailable
      decideInput available innerSource concreteProviders familyProviders location
    let proofMotive ← withLocalDeclD `target type fun target => do
      let equalityType ← mkAppM ``Eq #[sourceAt, target]
      withLocalDeclD `equality equalityType fun targetEquality => do
        let transported := mkAppN reduced.getAppFn
          #[type, sourceAt, sourceMotive, innerSource, target, targetEquality]
        let property ← mkSourceAvailableExpr body childContracts
          inputAvailable available transported
        mkLambdaFVars #[target, targetEquality] property
    let sourceLevels := reduced.getAppFn.constLevels!
    let proofRec := mkConst ``Eq.rec [.zero, sourceLevels[1]!]
    pure <| mkAppN proofRec
      #[type, sourceAt, proofMotive, innerProof, to, equality]
  else
    let property ← mkSourceAvailableExpr body childContracts
      inputAvailable available reduced
    let (proof, goals) ← casesOnWiringParameters property
    for goal in goals do
      goal.withContext do
        let target ← goal.getType
        let (targetName, targetArguments) := target.getAppFnArgs
        unless targetName == ``sourceAvailable && targetArguments.size >= 6 do
          throwError "`derive_schedule` could not expose wiring at {location}:{indentExpr target}"
        let specializedBody := targetArguments[targetArguments.size - 6]!
        let specializedChildContracts := targetArguments[targetArguments.size - 5]!
        let specializedInputAvailable := targetArguments[targetArguments.size - 3]!
        let specializedAvailable := targetArguments[targetArguments.size - 2]!
        let specializedSource := targetArguments.back!
        let inputDecidableEq ← mkInputDecidableEq specializedBody
        let specializedDecideInput ← mkDecideInput
          specializedInputAvailable inputDecidableEq
        let concrete ← try
          let occurrences ← exprList specializedAvailable
          let mut providers : List ConcreteProvider := []
          for (occurrence, index) in occurrences.zipIdx do
            providers := providers ++
              [⟨occurrence, ← membershipAt specializedAvailable index⟩]
          pure providers
        catch _ => pure concreteProviders
        let specializedFamilies ← match ← familyProviderFromAvailability?
            specializedAvailable with
          | some family => pure [family]
          | none => pure familyProviders
        let branchProof ← proveSourceAvailable specializedBody
          specializedChildContracts specializedInputAvailable specializedDecideInput
          specializedAvailable specializedSource concrete specializedFamilies location
        goal.assign branchProof
    instantiateMVars proof

private def buildReadCertificates
    (body childContracts inputAvailable decideInput available occurrence : Expr)
    (concreteProviders : List ConcreteProvider)
    (familyProviders : List FamilyProvider)
    (step : Nat) : MetaM Expr := do
  let reads ← mkAppM ``RuleOccurrence.reads #[occurrence]
  let inputs ← exprList reads
  let inputType := (← whnf (← inferType reads)).getAppArgs[0]!
  let child ← mkAppM ``RuleOccurrence.child #[occurrence]
  let wiring ← mkAppM ``ModuleBody.wiring #[body]
  let valueFunction ← withLocalDeclD `input inputType fun input => do
    let source ← mkAppM ``Wiring.instanceInput #[wiring, child, input]
    let property ← mkSourceAvailableExpr body childContracts
      inputAvailable available source
    let lifted ← mkAppM ``PLift #[property]
    mkLambdaFVars #[input] lifted
  let mut certificates := mkAppN (mkConst ``DependentList.nil [.zero, .zero])
    #[inputType, valueFunction]
  let mut certificateKeys := mkApp (mkConst ``List.nil [.zero]) inputType
  for (input, reverseIndex) in inputs.reverse.zipIdx do
    let readIndex := inputs.length - reverseIndex - 1
    let source ← mkAppM ``Wiring.instanceInput #[wiring, child, input]
    let proof ← proveSourceAvailable body childContracts inputAvailable decideInput
      available source concreteProviders familyProviders m!"rule {step}, read {readIndex}"
    let liftedProof ← mkAppM ``PLift.up #[proof]
    certificates := mkAppN (mkConst ``DependentList.cons [.zero, .zero])
      #[inputType, valueFunction, input, certificateKeys, liftedProof, certificates]
    certificateKeys := mkApp3 (mkConst ``List.cons [.zero]) inputType input certificateKeys
  pure certificates

private def isNullaryConstructorType (type : Expr) : MetaM Bool := do
  let reduced ← withTransparency .all <| whnf type
  let some name := reduced.getAppFn.constName? | return false
  match (← getEnv).find? name with
  | some (.inductInfo info) =>
      for constructor in info.ctors do
        match (← getEnv).find? constructor with
        | some (.ctorInfo value) =>
            if value.numFields != 0 then return false
        | _ => return false
      return true
  | _ => return false

/-- Prove a rule's reads directly when its input family is symbolic and cannot
be enumerated during elaboration. The arbitrary input is pushed through the
wiring function, after which the same source-availability logic applies. -/
private def buildSymbolicReadsProof
    (body childContracts inputAvailable decideInput available occurrence : Expr)
    (concreteProviders : List ConcreteProvider)
    (familyProviders : List FamilyProvider) (step : Nat) : MetaM Expr := do
  let reads ← mkAppM ``RuleOccurrence.reads #[occurrence]
  let inputType := (← whnf (← inferType reads)).getAppArgs[0]!
  let child ← mkAppM ``RuleOccurrence.child #[occurrence]
  let wiring ← mkAppM ``ModuleBody.wiring #[body]
  withLocalDeclD `input inputType fun input => do
    let memberType ← mkAppM ``List.Mem #[input, reads]
    withLocalDeclD `member memberType fun member => do
      let source ← mkAppM ``Wiring.instanceInput #[wiring, child, input]
      let target ← mkSourceAvailableExpr body childContracts
        inputAvailable available source
      let reducedReads ← withTransparency .all <| whnf reads
      if reducedReads.getAppFn.constName? == some ``List.nil then
        let impossible ← withTransparency .all <|
          mkAppM ``List.not_mem_nil #[member]
        let proof := mkAppN (mkConst ``False.elim [.zero]) #[target, impossible]
        return ← mkLambdaFVars #[input, member] proof
      let impossible ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
      let (remaining, _) ← Lean.Elab.runTactic impossible.mvarId!
        (← `(tactic| first
          | cases member
          | (change input ∈ [] at member; cases member)
          | simp_all [RuleOccurrence.reads, SignalSelection.labels]))
      if remaining.isEmpty then
        let proof := mkAppN (mkConst ``False.elim [.zero]) #[target, impossible]
        return ← mkLambdaFVars #[input, member] proof
      if ← isNullaryConstructorType inputType then
        let caseGoal ← mkFreshExprSyntheticOpaqueMVar target
        let caseResults ← caseGoal.mvarId!.cases input.fvarId!
        for result in caseResults do
          let goal := result.mvarId
          goal.withContext do
            let specializedTarget ← goal.getType
            let targetArguments := specializedTarget.getAppArgs
            let specializedBody := targetArguments[targetArguments.size - 6]!
            let specializedChildContracts :=
              targetArguments[targetArguments.size - 5]!
            let specializedInputAvailable :=
              targetArguments[targetArguments.size - 3]!
            let specializedAvailable := targetArguments[targetArguments.size - 2]!
            let specializedSource := targetArguments.back!
            let inputDecidableEq ← mkInputDecidableEq specializedBody
            let specializedDecideInput ← mkDecideInput
              specializedInputAvailable inputDecidableEq
            let proof ← proveSourceAvailable specializedBody
              specializedChildContracts specializedInputAvailable
              specializedDecideInput specializedAvailable specializedSource
              concreteProviders familyProviders
              m!"rule {step}, symbolic read case"
            goal.assign proof
        return ← mkLambdaFVars #[input, member] (← instantiateMVars caseGoal)
      let proof ← proveSourceAvailable body childContracts inputAvailable decideInput
        available source concreteProviders familyProviders
          m!"rule {step}, symbolic read from {indentExpr reads} with evidence {indentExpr memberType}"
      mkLambdaFVars #[input, member] proof

private def classifyFinish (Finish : Expr) : MetaM FinishKind := do
  let finish := Finish.getAppFnArgs
  if finish.1 == ``BoundaryReady && finish.2.size == 4 then
    pure (.outputs finish.2[2]!)
  else if finish.1 == ``ChildrenStateInputsReady && finish.2.size == 2 then
    pure .state
  else
    throwError "`derive_schedule` expects an `OutputSchedule` or `StateSchedule`, got final condition:{indentExpr Finish}"

private def buildOutputBoundary
    (body childContracts inputAvailable decideInput available outputs : Expr)
    (concreteProviders : List ConcreteProvider)
    (familyProviders : List FamilyProvider) : MetaM Expr := do
  let outputLabels ← exprList outputs
  let outputType := (← whnf (← inferType outputs)).getAppArgs[0]!
  let wiring ← mkAppM ``ModuleBody.wiring #[body]
  let valueFunction ← withLocalDeclD `output outputType fun output => do
    let source ← mkAppM ``Wiring.moduleOutput #[wiring, output]
    let property ← mkSourceAvailableExpr body childContracts
      inputAvailable available source
    let lifted ← mkAppM ``PLift #[property]
    mkLambdaFVars #[output] lifted
  let mut certificates := mkAppN (mkConst ``DependentList.nil [.zero, .zero])
    #[outputType, valueFunction]
  let mut certificateKeys := mkApp (mkConst ``List.nil [.zero]) outputType
  for (output, reverseIndex) in outputLabels.reverse.zipIdx do
    let outputIndex := outputLabels.length - reverseIndex - 1
    let source ← mkAppM ``Wiring.moduleOutput #[wiring, output]
    let proof ← proveSourceAvailable body childContracts inputAvailable decideInput
      available source concreteProviders familyProviders m!"required output {outputIndex}"
    let liftedProof ← mkAppM ``PLift.up #[proof]
    certificates := mkAppN (mkConst ``DependentList.cons [.zero, .zero])
      #[outputType, valueFunction, output, certificateKeys, liftedProof, certificates]
    certificateKeys := mkApp3 (mkConst ``List.cons [.zero])
      outputType output certificateKeys
  withTransparency .all <| mkAppM ``ScheduleDerivation.boundaryReady_of_certificates
    #[outputs, inputAvailable, available, certificates]

private def stateReadLabels (childContracts child : Expr) : MetaM Expr := do
  let contract := mkApp childContracts child
  let stateRule ← mkAppM ``ModuleCycleContract.stateRule #[contract]
  let reads ← mkAppM ``CycleStateRule.readsInputs #[stateRule]
  mkAppM ``SignalSelection.labels #[reads]

private def buildStateChildCertificates
    (body childContracts inputAvailable decideInput available child : Expr)
    (concreteProviders : List ConcreteProvider)
    (familyProviders : List FamilyProvider) : MetaM Expr := do
  let inputs ← stateReadLabels childContracts child
  let inputLabels ← exprList inputs
  let inputType := (← whnf (← inferType inputs)).getAppArgs[0]!
  let wiring ← mkAppM ``ModuleBody.wiring #[body]
  let valueFunction ← withLocalDeclD `input inputType fun input => do
    let source ← mkAppM ``Wiring.instanceInput #[wiring, child, input]
    let signalType := (← withTransparency .reducible <| whnf (← inferType source))
      |>.getAppArgs.back!
    let property := mkAppN (mkConst ``sourceAvailable)
      #[body, childContracts, signalType, inputAvailable, available, source]
    let lifted ← mkAppM ``PLift #[property]
    mkLambdaFVars #[input] lifted
  let mut certificates := mkAppN (mkConst ``DependentList.nil [.zero, .zero])
    #[inputType, valueFunction]
  let mut certificateKeys := mkApp (mkConst ``List.nil [.zero]) inputType
  for (input, reverseIndex) in inputLabels.reverse.zipIdx do
    let inputIndex := inputLabels.length - reverseIndex - 1
    let source ← mkAppM ``Wiring.instanceInput #[wiring, child, input]
    let proof ← proveSourceAvailable body childContracts inputAvailable decideInput
      available source concreteProviders familyProviders
        m!"state input {inputIndex} of child {indentExpr child}"
    let liftedProof ← mkAppM ``PLift.up #[proof]
    certificates := mkAppN (mkConst ``DependentList.cons [.zero, .zero])
      #[inputType, valueFunction, input, certificateKeys, liftedProof, certificates]
    certificateKeys := mkApp3 (mkConst ``List.cons [.zero])
      inputType input certificateKeys
  pure certificates

private def isEmptyOrUnitType (type : Expr) : MetaM Bool := do
  let reduced ← withTransparency .all <| whnf type
  let some name := reduced.getAppFn.constName? | return false
  if name == ``PUnit || name == ``Sum then return true
  match (← getEnv).find? name with
  | some (.inductInfo info) =>
      if info.ctors.isEmpty then return true
      for constructor in info.ctors do
        match (← getEnv).find? constructor with
        | some (.ctorInfo value) =>
            if value.numFields != 0 then return false
        | _ => return false
      return true
  | _ => return false

private partial def caseEmptyOrUnitLocals (goal : MVarId) : MetaM (List MVarId) :=
  goal.withContext do
    for fvarId in (← getLCtx).getFVarIds.reverse do
      let declaration ← fvarId.getDecl
      let userName := declaration.userName.eraseMacroScopes
      if userName == `rule || userName == `member then
        continue
      if ← isEmptyOrUnitType declaration.type then
        let subgoals ← goal.cases fvarId
        let mut result := []
        for subgoal in subgoals do
          result := result ++ (← caseEmptyOrUnitLocals subgoal.mvarId)
        return result
    return [goal]

private def isStructuralIndexType (type : Expr) : MetaM Bool := do
  let reduced ← withTransparency .reducible <| whnf type
  let some name := reduced.getAppFn.constName? | return false
  if name == ``PUnit || name == ``Sum then return true
  match (← getEnv).find? name with
  | some (.inductInfo info) => return info.ctors.isEmpty
  | _ => return false

private partial def caseStructuralIndexLocals
    (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  for fvarId in (← getLCtx).getFVarIds.reverse do
    let declaration ← fvarId.getDecl
    let userName := declaration.userName.eraseMacroScopes
    if userName == `rule || userName == `member then
      continue
    if ← isStructuralIndexType declaration.type then
      let subgoals ← goal.cases fvarId
      let mut result := []
      for subgoal in subgoals do
        result := result ++ (← caseStructuralIndexLocals subgoal.mvarId)
      return result
  return [goal]

private def closeEmptyMembershipGoal? (goal : MVarId) : MetaM Bool :=
  goal.withContext do
    for fvarId in (← getLCtx).getFVarIds do
      let declaration ← fvarId.getDecl
      let type ← withTransparency .all <| whnf declaration.type
      let (name, arguments) := type.getAppFnArgs
      if name == ``List.Mem && arguments.size == 3 then
        let values := arguments.back!
        let entries? ← try pure (some (← exprList values)) catch _ => pure none
        if entries? == some [] then
          let impossible ← withTransparency .all <|
            mkAppM ``List.not_mem_nil #[mkFVar fvarId]
          let target ← goal.getType
          goal.assign (mkAppN (mkConst ``False.elim [.zero]) #[target, impossible])
          return true
    return false

private def buildStateBoundary
    (body childContracts inputAvailable decideInput available : Expr)
    (concreteProviders : List ConcreteProvider)
    (familyProviders : List FamilyProvider) : MetaM Expr := do
  if familyProviders.isEmpty then
    let directTarget := mkAppN (mkConst ``ChildrenStateInputsReady)
      #[body, childContracts, available]
    let directGoal ← mkFreshExprSyntheticOpaqueMVar directTarget
    let (afterIntro, _) ← Lean.Elab.runTactic directGoal.mvarId!
      (← `(tactic| intro child input member))
    let mut directRemaining := []
    for current in afterIntro do
      let childId? ← current.withContext do
        let mut result : Option FVarId := none
        for id in (← getLCtx).getFVarIds do
          let declaration ← id.getDecl
          if declaration.userName.eraseMacroScopes == `child then
            result := some id
        pure result
      let firstCases ← match childId? with
        | some childId => pure <| (← current.cases childId).toList.map (·.mvarId)
        | none => pure [current]
      let mut afterCases := []
      for firstCase in firstCases do
        for structuralCase in (← caseStructuralIndexLocals firstCase) do
          afterCases := afterCases ++ (← caseEmptyOrUnitLocals structuralCase)
      for branch in afterCases do
        let (next, _) ← Lean.Elab.runTactic branch
          (← `(tactic| dsimp at member <;>
            simp_all [CycleStateRule.empty, SignalMap.select,
              SignalSelection.labels]))
        for goal in next do
          unless ← closeEmptyMembershipGoal? goal do
            directRemaining := directRemaining ++ [goal]
    if directRemaining.isEmpty then
      return ← instantiateMVars directGoal
  let context ← mkAppM ``ModuleBody.context #[body]
  let instancePorts ← mkAppM ``EndpointContext.instancePorts #[context]
  let names ← mkAppM ``EnumeratedMap.keys #[instancePorts]
  let childType := (← whnf (← inferType names)).getAppArgs[0]!
  let children := mkAppN (mkConst ``Enumeration.values [.zero]) #[childType, names]
  let childLabels? ← try
    pure (some (← exprList children))
  catch _ => pure none
  if childLabels?.isNone then
    let target := mkAppN (mkConst ``ChildrenStateInputsReady)
      #[body, childContracts, available]
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    let (afterIntro, _) ← Lean.Elab.runTactic goal.mvarId!
      (← `(tactic| intro child input member))
    let mut afterCases := []
    for current in afterIntro do
      let (next, _) ← Lean.Elab.runTactic current (← `(tactic| cases child))
      afterCases := afterCases ++ next
    let mut remaining := []
    for current in afterCases do
      let (next, _) ← Lean.Elab.runTactic current
        (← `(tactic| dsimp at member <;>
          simp_all [CycleStateRule.empty, SignalMap.select,
            SignalSelection.labels]))
      for goal in next do
        unless ← closeEmptyMembershipGoal? goal do
          remaining := remaining ++ [goal]
    for unsolved in remaining do
      unsolved.withContext do
        let (caseProof, caseGoals) ← casesOnStateBoundaryInput (← unsolved.getType)
        for caseGoal in caseGoals do
          caseGoal.withContext do
            let target ← caseGoal.getType
            let (targetName, targetArguments) := target.getAppFnArgs
            unless targetName == ``sourceAvailable && targetArguments.size >= 6 do
              throwError
                "`derive_schedule` cannot expose this symbolic state boundary:{indentExpr target}"
            let specializedBody := targetArguments[targetArguments.size - 6]!
            let specializedChildContracts :=
              targetArguments[targetArguments.size - 5]!
            let specializedInputAvailable :=
              targetArguments[targetArguments.size - 3]!
            let specializedAvailable := targetArguments[targetArguments.size - 2]!
            let specializedSource := targetArguments.back!
            let inputDecidableEq ← mkInputDecidableEq specializedBody
            let specializedDecideInput ← mkDecideInput
              specializedInputAvailable inputDecidableEq
            let proof ← proveSourceAvailable specializedBody
              specializedChildContracts specializedInputAvailable specializedDecideInput
              specializedAvailable specializedSource concreteProviders familyProviders
              "symbolic state boundary"
            caseGoal.assign proof
        unsolved.assign (← instantiateMVars caseProof)
    return (← instantiateMVars goal)
  let childLabels := childLabels?.get!
  let wiring ← mkAppM ``ModuleBody.wiring #[body]
  let outerValueFunction ← withLocalDeclD `child childType fun child => do
    let inputs ← stateReadLabels childContracts child
    let inputType := (← whnf (← inferType inputs)).getAppArgs[0]!
    let innerValueFunction ← withLocalDeclD `input inputType fun input => do
      let source ← mkAppM ``Wiring.instanceInput #[wiring, child, input]
      let signalType := (← withTransparency .reducible <| whnf (← inferType source))
        |>.getAppArgs.back!
      let property := mkAppN (mkConst ``sourceAvailable)
        #[body, childContracts, signalType, inputAvailable, available, source]
      let lifted ← mkAppM ``PLift #[property]
      mkLambdaFVars #[input] lifted
    let innerType := mkAppN (mkConst ``DependentList [.zero, .zero])
      #[inputType, innerValueFunction, inputs]
    mkLambdaFVars #[child] innerType
  let mut certificates := mkAppN (mkConst ``DependentList.nil [.zero, .zero])
    #[childType, outerValueFunction]
  let mut certificateKeys := mkApp (mkConst ``List.nil [.zero]) childType
  for child in childLabels.reverse do
    let childCertificates ← buildStateChildCertificates body childContracts
      inputAvailable decideInput available child concreteProviders familyProviders
    certificates := mkAppN (mkConst ``DependentList.cons [.zero, .zero])
      #[childType, outerValueFunction, child, certificateKeys,
        childCertificates, certificates]
    certificateKeys := mkApp3 (mkConst ``List.cons [.zero])
      childType child certificateKeys
  withTransparency .all <| pure <| mkAppN
    (mkConst ``ScheduleDerivation.stateBoundaryReady_of_certificates)
    #[body, childContracts, available, certificates]

private partial def buildSchedule
    (body childContracts inputAvailable decideInput Finish : Expr)
    (finishKind : FinishKind)
    (ordered : List OrderStep) (available : Expr)
    (concreteProviders : List ConcreteProvider)
    (familyProviders : List FamilyProvider)
    (step : Nat) : MetaM Expr := do
  match ordered with
  | [] =>
      let finished ← match finishKind with
        | .outputs outputs =>
            buildOutputBoundary body childContracts inputAvailable decideInput
              available outputs concreteProviders familyProviders
        | .state =>
            buildStateBoundary body childContracts inputAvailable decideInput
              available concreteProviders familyProviders
      pure <| mkAppN (mkConst ``Schedule.done)
        #[body, childContracts, inputAvailable, Finish, available, finished]
  | .call occurrence :: rest =>
      let freshCheck ← mkAppM ``ScheduleDerivation.freshBool #[available, occurrence]
      let fresh ← if ← withTransparency .all <| isDefEq freshCheck (mkConst ``true) then
        let freshProof ← mkEqRefl freshCheck
        mkAppM ``ScheduleDerivation.fresh_of_bool_eq_true
          #[available, occurrence, freshProof]
      else
        let mut familyProof? : Option Expr := none
        let mut precedingCalls : List Expr := []
        let mut familyTail := available
        let mut peeling := true
        while peeling do
          let (tailName, tailArguments) := familyTail.getAppFnArgs
          if tailName == ``List.cons && tailArguments.size == 3 then
            precedingCalls := precedingCalls ++ [tailArguments[1]!]
            familyTail := tailArguments[2]!
          else
            peeling := false
        for family in familyProviders do
          let familyFinal ← mkAppM ``Schedule.finalAvailability #[family.schedule]
          if ← sameExpr familyFinal familyTail then
            let oldCheck ← mkAppM ``ScheduleDerivation.childFreshBool
              #[family.initial, occurrence]
            if ← withTransparency .all <| isDefEq oldCheck (mkConst ``true) then
              let oldCheckProof ← mkEqRefl oldCheck
              let oldChildDifferent ← mkAppM
                ``ScheduleDerivation.child_fresh_of_bool_eq_true
                  #[family.initial, occurrence, oldCheckProof]
              let familyDifferent ← withLocalDeclD `index family.indexType fun index => do
                let called := mkApp family.occurrence index
                let check ← mkAppM ``ScheduleDerivation.childrenDifferentBool
                  #[occurrence, called]
                let proof ← if ← withTransparency .all <|
                    isDefEq check (mkConst ``true) then
                  let checkProof ← mkEqRefl check
                  mkAppM ``ScheduleDerivation.children_different_of_bool_eq_true
                    #[occurrence, called, checkProof]
                else
                  proveChildDifferent occurrence called
                    m!"rule {step} disjointness from preceding family"
                mkLambdaFVars #[index] proof
              let mut proof ← mkAppM
                ``ScheduleDerivation.fresh_after_family_of_child_disjoint
                  #[family.initial, family.indices, family.occurrence,
                    family.injective, family.fresh, family.reads, occurrence,
                    oldChildDifferent, familyDifferent]
              for head in precedingCalls.reverse do
                let different ← proveChildDifferent occurrence head
                  m!"rule {step} disjointness from preceding call"
                proof ← mkAppM ``ScheduleDerivation.fresh_cons_of_child_disjoint
                  #[occurrence, head, familyTail, different, proof]
                familyTail ← mkAppM ``List.cons #[head, familyTail]
              familyProof? := some proof
        match familyProof? with
        | some proof => pure proof
        | none =>
            proveFreshFromAvailability occurrence available familyProviders
              m!"freshness of rule {step}"
      let occurrenceReads ← mkAppM ``RuleOccurrence.reads #[occurrence]
      let concreteReads? ← try
        pure (some (← exprList occurrenceReads))
      catch _ => pure none
      let reads ← if concreteReads?.isSome then
        let certificates ← buildReadCertificates body childContracts inputAvailable
          decideInput available occurrence concreteProviders familyProviders step
        withTransparency .all <|
          mkAppM ``ScheduleDerivation.readsAvailable_of_certificates
            #[inputAvailable, available, occurrence, certificates]
      else
        buildSymbolicReadsProof body childContracts inputAvailable decideInput
          available occurrence concreteProviders familyProviders step
      let nextAvailable ← mkAppM ``List.cons #[occurrence, available]
      let occurrenceType ← inferType occurrence
      let newMember := mkAppN (mkConst ``List.mem_cons_self [.zero])
        #[occurrenceType, occurrence, available]
      let mut nextConcrete : List ConcreteProvider :=
        [⟨occurrence, newMember⟩]
      for provider in concreteProviders do
        let member ← mkAppM ``List.mem_cons_of_mem #[occurrence, provider.member]
        nextConcrete := nextConcrete ++ [⟨provider.occurrence, member⟩]
      let mut nextFamilies : List FamilyProvider := []
      for family in familyProviders do
        let member ← withLocalDeclD `index family.indexType fun index => do
          let oldMember := mkApp family.member index
          let lifted ← mkAppM ``List.mem_cons_of_mem #[occurrence, oldMember]
          mkLambdaFVars #[index] lifted
        nextFamilies := nextFamilies ++ [{ family with member := member }]
      let tail ← buildSchedule body childContracts inputAvailable decideInput Finish
        finishKind rest nextAvailable nextConcrete nextFamilies (step + 1)
      pure <| mkAppN (mkConst ``Schedule.call)
        #[body, childContracts, inputAvailable, Finish, available,
          occurrence, reads, fresh, tail]
  | .family indexType indices occurrence :: rest =>
      let injectiveType ← mkAppM ``Function.Injective #[occurrence]
      let injective ← proveOccurrenceFamilyInjective injectiveType
        m!"injectivity of rule family {step}"
      let fresh ← withLocalDeclD `index indexType fun index => do
        let called := mkApp occurrence index
        let check ← mkAppM ``ScheduleDerivation.childFreshBool #[available, called]
        let proof ← if ← withTransparency .all <|
            isDefEq check (mkConst ``true) then
          let checkProof ← mkEqRefl check
          mkAppM ``ScheduleDerivation.fresh_of_child_bool_eq_true
            #[available, called, checkProof]
        else
          proveFreshFromAvailability called available familyProviders
            m!"freshness of rule family {step}"
        mkLambdaFVars #[index] proof
      let reads ← withLocalDeclD `index indexType fun index => do
        let called := mkApp occurrence index
        let proof ← buildSymbolicReadsProof body childContracts inputAvailable
          decideInput available called concreteProviders familyProviders step
        mkLambdaFVars #[index] proof
      let familySchedule ← mkAppM ``Schedule.callFamilyAfter
        #[available, indices, occurrence, injective, fresh, reads]
      let familyFinal ← mkAppM ``Schedule.finalAvailability #[familySchedule]
      let familyFinished ← mkAppM ``Schedule.finished #[familySchedule]
      let includesOld := mkProj ``And 0 familyFinished
      let familyFacts := mkProj ``And 1 familyFinished
      let includesFamily := mkProj ``And 0 familyFacts
      let mut nextConcrete : List ConcreteProvider := []
      for provider in concreteProviders do
        let member := mkApp2 includesOld provider.occurrence provider.member
        nextConcrete := nextConcrete ++ [⟨provider.occurrence, member⟩]
      let mut nextFamilies : List FamilyProvider := []
      for family in familyProviders do
        let member ← withLocalDeclD `index family.indexType fun index => do
          let oldMember := mkApp family.member index
          let called := mkApp family.occurrence index
          mkLambdaFVars #[index] (mkApp2 includesOld called oldMember)
        nextFamilies := nextFamilies ++ [{ family with member := member }]
      let familyMember ← withLocalDeclD `index indexType fun index =>
        mkLambdaFVars #[index] (mkApp includesFamily index)
      nextFamilies := nextFamilies ++ [⟨indexType, available, indices, occurrence,
        injective, fresh, reads, familySchedule, familyMember⟩]
      let tail ← buildSchedule body childContracts inputAvailable decideInput Finish
        finishKind rest familyFinal nextConcrete nextFamilies (step + 1)
      mkAppM ``Schedule.append #[familySchedule, tail]

private def deriveScheduleExpr (target ordered : Expr) : MetaM Expr := do
  let target ← withTransparency .reducible <| whnf target
  let (targetName, targetArgs) := target.getAppFnArgs
  unless targetName == ``Schedule && targetArgs.size == 5 do
    throwError "schedule derivation expects an output or state schedule type"
  let body := targetArgs[0]!
  let childContracts := targetArgs[1]!
  let inputAvailable ← instantiateMVars targetArgs[2]!
  let Finish ← instantiateMVars targetArgs[3]!
  let initial := targetArgs[4]!
  let inputDecidableEq ← mkInputDecidableEq body
  let decideInput ← mkDecideInput inputAvailable inputDecidableEq
  let finishKind ← classifyFinish Finish
  let calls ← orderSteps ordered
  let initiallyAvailable ← exprList initial
  let mut initialProviders : List ConcreteProvider := []
  for (occurrence, index) in initiallyAvailable.zipIdx do
    initialProviders := initialProviders ++ [⟨occurrence, ← membershipAt initial index⟩]
  buildSchedule body childContracts inputAvailable decideInput Finish finishKind
    calls initial initialProviders [] 0

private def ruleNamesValues (contract : Expr) : MetaM (Expr × Expr) := do
  let names ← mkAppM ``ModuleCycleContract.ruleNames #[contract]
  let nameType := (← whnf (← inferType names)).getAppArgs[0]!
  let values := mkAppN (mkConst ``Enumeration.values [.zero]) #[nameType, names]
  pure (nameType, values)

private def ruleNamesList (contract : Expr) : MetaM (Expr × Expr × List Expr) := do
  let (nameType, values) ← ruleNamesValues contract
  pure (nameType, values, ← exprList values)

private def childNamesList (body : Expr) : MetaM (Expr × Expr × List Expr) := do
  let context ← mkAppM ``ModuleBody.context #[body]
  let ports ← mkAppM ``EndpointContext.instancePorts #[context]
  let names ← mkAppM ``EnumeratedMap.keys #[ports]
  let nameType := (← whnf (← inferType names)).getAppArgs[0]!
  let values := mkAppN (mkConst ``Enumeration.values [.zero]) #[nameType, names]
  pure (nameType, values, ← exprList values)

private def coverageProperty
    (body childContracts schedules child rule : Expr) : MetaM Expr := do
  let occurrence := mkAppN (mkConst ``RuleOccurrence.mk)
    #[body, childContracts, child, rule]
  let state ← mkAppM ``RuleSchedules.state #[schedules]
  let stateFinal ← mkAppM ``Schedule.finalAvailability #[state]
  let stateMember ← mkAppM ``List.Mem #[occurrence, stateFinal]
  let contract := (← whnf (← inferType schedules)).getAppArgs[2]!
  let ruleName ← mkAppM ``ModuleCycleContract.RuleName #[contract]
  let outputExists ← withLocalDeclD `name ruleName fun name => do
    let output ← mkAppM ``RuleSchedules.output #[schedules, name]
    let outputFinal ← mkAppM ``Schedule.finalAvailability #[output]
    let member ← mkAppM ``List.Mem #[occurrence, outputFinal]
    let predicate ← mkLambdaFVars #[name] member
    mkAppM ``Exists #[predicate]
  mkAppM ``Or #[stateMember, outputExists]

private def scheduleMemberAt (schedule : Expr) (orderedLength position : Nat) : MetaM Expr := do
  let final ← mkAppM ``Schedule.finalAvailability #[schedule]
  membershipAt final (orderedLength - position - 1)

private def buildCoverageProof
    (body childContracts schedules stateSchedule : Expr)
    (stateOrder : List Expr)
    (outputNames : List Expr) (outputOrders : List (List Expr))
    (outputSchedules : List Expr) : MetaM Expr := do
  let (childType, _children, childLabels) ← childNamesList body
  let outerValue ← withLocalDeclD `child childType fun child => do
    let childContract := mkApp childContracts child
    let (ruleType, rules) ← ruleNamesValues childContract
    let innerValue ← withLocalDeclD `rule ruleType fun rule => do
      let property ← coverageProperty body childContracts schedules child rule
      let lifted ← mkAppM ``PLift #[property]
      mkLambdaFVars #[rule] lifted
    let innerType := mkAppN (mkConst ``DependentList [.zero, .zero])
      #[ruleType, innerValue, rules]
    mkLambdaFVars #[child] innerType
  let mut outerCertificates := mkAppN (mkConst ``DependentList.nil [.zero, .zero])
    #[childType, outerValue]
  let mut outerKeys := mkApp (mkConst ``List.nil [.zero]) childType
  for child in childLabels.reverse do
    let childContract := mkApp childContracts child
    let (ruleType, _rules, ruleLabels) ← ruleNamesList childContract
    let innerValue ← withLocalDeclD `rule ruleType fun rule => do
      let property ← coverageProperty body childContracts schedules child rule
      let lifted ← mkAppM ``PLift #[property]
      mkLambdaFVars #[rule] lifted
    let mut innerCertificates := mkAppN (mkConst ``DependentList.nil [.zero, .zero])
      #[ruleType, innerValue]
    let mut innerKeys := mkApp (mkConst ``List.nil [.zero]) ruleType
    for rule in ruleLabels.reverse do
      let occurrence := mkAppN (mkConst ``RuleOccurrence.mk)
        #[body, childContracts, child, rule]
      let property ← coverageProperty body childContracts schedules child rule
      let propertyArgs := property.getAppArgs
      let stateProperty := propertyArgs[propertyArgs.size - 2]!
      let outputProperty := propertyArgs.back!
      let mut witness? : Option Expr := none
      for (called, position) in stateOrder.zipIdx do
        if ← sameExpr occurrence called then
          let member ← scheduleMemberAt stateSchedule stateOrder.length position
          witness? := some (mkAppN (mkConst ``Or.inl)
            #[stateProperty, outputProperty, member])
      if witness?.isNone then
        for ((name, order), schedule) in
            (outputNames.zip outputOrders).zip outputSchedules do
          for (called, position) in order.zipIdx do
            if ← sameExpr occurrence called then
              let member ← scheduleMemberAt schedule order.length position
              let outputArgs := outputProperty.getAppArgs
              let existsProof := mkAppN (mkConst ``Exists.intro [.succ .zero])
                #[outputArgs[0]!, outputArgs[1]!, name, member]
              witness? := some (mkAppN (mkConst ``Or.inr)
                #[stateProperty, outputProperty, existsProof])
      let witness ← witness?.getDM do
        throwError "rule schedules do not cover child rule:{indentExpr occurrence}"
      let lifted ← mkAppM ``PLift.up #[witness]
      innerCertificates := mkAppN (mkConst ``DependentList.cons [.zero, .zero])
        #[ruleType, innerValue, rule, innerKeys, lifted, innerCertificates]
      innerKeys := mkApp3 (mkConst ``List.cons [.zero]) ruleType rule innerKeys
    outerCertificates := mkAppN (mkConst ``DependentList.cons [.zero, .zero])
      #[childType, outerValue, child, outerKeys, innerCertificates, outerCertificates]
    outerKeys := mkApp3 (mkConst ``List.cons [.zero]) childType child outerKeys
  withTransparency .all <| mkAppM ``ScheduleDerivation.coversChildren_of_certificates
    #[schedules, outerCertificates]

private def proveScheduleMembership (occurrence schedule : Expr) : MetaM Expr := do
  let final ← mkAppM ``Schedule.finalAvailability #[schedule]
  let target ← mkAppM ``List.Mem #[occurrence, final]
  let proof ← mkFreshExprSyntheticOpaqueMVar target
  let (simplifiedGoals, _) ← Lean.Elab.runTactic proof.mvarId!
    (← `(tactic| simp only [Schedule.finalAvailability_call,
      Schedule.finalAvailability_append]))
  let simplifiedGoal ← match simplifiedGoals with
    | [goal] => pure goal
    | _ => throwError "could not expose final schedule availability"
  simplifiedGoal.withContext do
    let simplifiedType ← simplifiedGoal.getType
    let simplifiedArguments := simplifiedType.getAppArgs
    unless simplifiedArguments.size >= 2 do
      throwError "unexpected schedule-membership goal:{indentExpr simplifiedType}"
    let directProof ← findProviderMembership occurrence simplifiedArguments.back!
    simplifiedGoal.assign directProof
  instantiateMVars proof

private def constructorCandidates (type : Expr) : MetaM (List Expr) := do
  let reduced ← withTransparency .all <| whnf type
  let some name := reduced.getAppFn.constName? | return []
  let some (.inductInfo info) := (← getEnv).find? name | return []
  let mut candidates := []
  for constructor in info.ctors do
    let constant ← mkConstWithFreshMVarLevels constructor
    let (arguments, _, result) ← forallMetaTelescopeReducing (← inferType constant)
    if ← withTransparency .all <| isDefEq result reduced then
      candidates := candidates ++ [mkAppN constant arguments]
  return candidates

private def orderContainsOccurrence (ordered occurrence : Expr) : MetaM Bool := do
  for step in (← orderSteps ordered) do
    match step with
    | .call called =>
        if ← sameExpr occurrence called then return true
    | .family indexType _ occurrenceFamily =>
        let index ← mkFreshExprMVar (some indexType)
        if ← sameExpr occurrence (mkApp occurrenceFamily index) then return true
  return false

private def buildCoverageByTactic (orders schedules stateSchedule outputCertificates
    ruleNameValues : Expr) (parentNames : List Expr)
    (outputSchedules : List Expr) : MetaM Expr := do
  let schedulesType ← withTransparency .reducible <| whnf (← inferType schedules)
  let scheduleArguments := schedulesType.getAppArgs
  let target ← mkAppM ``RuleSchedules.CoversChildren #[schedules]
  let goal ← mkFreshExprSyntheticOpaqueMVar target
  let (afterIntro, _) ← Lean.Elab.runTactic goal.mvarId!
    (← `(tactic| intro child rule))
  let mut afterChildren := []
  for current in afterIntro do
    let (next, _) ← Lean.Elab.runTactic current (← `(tactic| cases child))
    afterChildren := afterChildren ++ next
  let mut afterRules := []
  for current in afterChildren do
    let structuralCases ← caseStructuralIndexLocals current
    for structuralCase in structuralCases do
      let (ruleCases, _) ← Lean.Elab.runTactic structuralCase
        (← `(tactic| cases rule))
      for ruleCase in ruleCases do
        afterRules := afterRules ++ (← caseEmptyOrUnitLocals ruleCase)
  for current in afterRules do
    current.withContext do
      let target ← current.getType
      let targetArguments := target.getAppArgs
      unless target.getAppFn.constName? == some ``Or && targetArguments.size == 2 do
        throwError "unexpected child-rule coverage goal:{indentExpr target}"
      let stateMembership := targetArguments[0]!
      let stateArguments := stateMembership.getAppArgs
      unless stateArguments.size >= 2 do
        throwError "unexpected state coverage goal:{indentExpr stateMembership}"
      let occurrence := stateArguments.back!
      let stateProof? ← try
        pure (some (← proveScheduleMembership occurrence stateSchedule))
      catch _ => pure none
      if let some stateProof := stateProof? then
        current.assign <| mkAppN (mkConst ``Or.inl)
          #[stateMembership, targetArguments[1]!, stateProof]
      else
        let outputExists := targetArguments[1]!
        let existsArguments := outputExists.getAppArgs
        unless outputExists.getAppFn.constName? == some ``Exists &&
            existsArguments.size == 2 do
          throwError "unexpected output coverage goal:{indentExpr outputExists}"
        let parentType := existsArguments[0]!
        let predicate := existsArguments[1]!
        let mut witness? : Option (Expr × Expr) := none
        for (parentName, directSchedule, position) in
            parentNames.zip outputSchedules |>.zipIdx |>.map
              (fun ((name, schedule), index) => (name, schedule, index)) do
          if witness?.isNone then
            try
              let directProof ← proveScheduleMembership occurrence directSchedule
              let parentIndex ← listIndexAt ruleNameValues position
              let transported := mkAppN
                (mkConst
                  ``ScheduleDerivation.outputSchedulesFromCertificates_mem_finalAvailability)
                #[scheduleArguments[0]!, scheduleArguments[1]!, scheduleArguments[2]!,
                  outputCertificates, parentName, parentIndex, occurrence, directProof]
              witness? := some (parentName, transported)
            catch _ => pure ()
        if witness?.isNone then
          for parentName in (← constructorCandidates parentType) do
            if witness?.isNone then
              try
                let ordered ← mkAppM ``ScheduleDerivation.RuleScheduleOrders.output
                  #[orders, parentName]
                unless ← orderContainsOccurrence ordered occurrence do
                  throwError "parent rule order does not contain occurrence"
                let parentName ← instantiateMVars parentName
                let directSchedule ← mkAppM ``RuleSchedules.output
                  #[schedules, parentName]
                let directProof ← proveScheduleMembership occurrence directSchedule
                witness? := some (← instantiateMVars parentName, directProof)
              catch _ => pure ()
        let (parentName, membership) ← witness?.getDM do
          throwError "scheduled rules do not contain child rule:{indentExpr occurrence}"
        let parentSort ← withTransparency .reducible <| whnf (← inferType parentType)
        let level := match parentSort with
          | .sort level => level
          | _ => .succ .zero
        let membershipType ← withTransparency .reducible <|
          whnf (mkApp predicate parentName)
        let membershipActual ← inferType membership
        unless ← isDefEq membershipActual membershipType do
          throwError "coverage membership has the wrong type:{indentExpr membershipActual}\nexpected:{indentExpr membershipType}"
        let existsProof := mkAppN (mkConst ``Exists.intro [level])
          #[parentType, predicate, parentName, membership]
        current.assign <| mkAppN (mkConst ``Or.inr)
          #[stateMembership, outputExists, existsProof]
  instantiateMVars goal

private def buildCompleteCoverageByTactic
    (body childContracts schedule : Expr) : MetaM Expr := do
  let final ← mkAppM ``Schedule.finalAvailability #[schedule]
  let target ← mkAppM ``CoversAllRules #[body, childContracts, final]
  let goal ← mkFreshExprSyntheticOpaqueMVar target
  let (afterIntro, _) ← Lean.Elab.runTactic goal.mvarId!
    (← `(tactic| intro child rule))
  let mut afterChildren := []
  for current in afterIntro do
    let (next, _) ← Lean.Elab.runTactic current (← `(tactic| cases child))
    afterChildren := afterChildren ++ next
  let mut ruleGoals := []
  for current in afterChildren do
    for structuralCase in (← caseStructuralIndexLocals current) do
      let (cases, _) ← Lean.Elab.runTactic structuralCase
        (← `(tactic| cases rule))
      for ruleCase in cases do
        ruleGoals := ruleGoals ++ (← caseEmptyOrUnitLocals ruleCase)
  for current in ruleGoals do
    current.withContext do
      let membership ← current.getType
      let arguments := membership.getAppArgs
      unless arguments.size >= 2 do
        throwError "unexpected complete-schedule coverage goal:{indentExpr membership}"
      let occurrence := arguments.back!
      current.assign (← proveScheduleMembership occurrence schedule)
  instantiateMVars goal

private def deriveCompleteScheduleExpr (target ordered : Expr) : MetaM Expr := do
  let target ← withTransparency .reducible <| whnf target
  let (name, arguments) := target.getAppFnArgs
  unless name == ``ScheduleDerivation.DerivedCompleteSchedule &&
      arguments.size == 2 do
    throwError "`derive_complete_schedule` expects a `DerivedCompleteSchedule` goal"
  let body := arguments[0]!
  let childContracts := arguments[1]!
  let stateType ← mkAppM ``StateSchedule #[body, childContracts]
  let schedule ← deriveScheduleExpr stateType ordered
  let coverage ← buildCompleteCoverageByTactic body childContracts schedule
  pure <| mkAppN (mkConst ``ScheduleDerivation.DerivedCompleteSchedule.mk)
    #[body, childContracts, schedule, coverage]

private def deriveSymbolicRuleSchedulesExpr
    (body childContracts contract orders ruleNameType : Expr) : MetaM Expr := do
  let outputFunctionType ← withLocalDeclD `name ruleNameType fun name => do
    let scheduleType ← mkAppM ``OutputSchedule
      #[body, childContracts, contract, name]
    mkForallFVars #[name] scheduleType
  let outputFunction ← mkFreshExprSyntheticOpaqueMVar outputFunctionType
  let (afterIntro, _) ← Lean.Elab.runTactic outputFunction.mvarId!
    (← `(tactic| intro name))
  let mut branches := []
  for goal in afterIntro do
    let (next, _) ← Lean.Elab.runTactic goal (← `(tactic| cases name))
    branches := branches ++ next
  for branch in branches do
    branch.withContext do
      let scheduleType ← branch.getType
      let (scheduleName, scheduleArguments) := scheduleType.getAppFnArgs
      unless scheduleName == ``OutputSchedule && scheduleArguments.size == 4 do
        throwError
          "`derive_rule_schedules` cannot expose a symbolic parent rule:{indentExpr scheduleType}"
      let parentName := scheduleArguments.back!
      let ordered ← mkAppM ``ScheduleDerivation.RuleScheduleOrders.output
        #[orders, parentName]
      let schedule ← deriveScheduleExpr scheduleType ordered
      branch.assign schedule
  let outputFunction ← instantiateMVars outputFunction
  let stateOrder ← mkAppM ``ScheduleDerivation.RuleScheduleOrders.state #[orders]
  let stateType ← mkAppM ``StateSchedule #[body, childContracts]
  let stateSchedule ← deriveScheduleExpr stateType stateOrder
  let schedules := mkAppN (mkConst ``RuleSchedules.mk)
    #[body, childContracts, contract, outputFunction, stateSchedule]
  let dummy := mkConst ``PUnit.unit
  let coverage ← buildCoverageByTactic orders schedules stateSchedule dummy dummy [] []
  pure <| mkAppN (mkConst ``ScheduleDerivation.DerivedRuleSchedules.mk)
    #[body, childContracts, contract, schedules, coverage]

private def deriveRuleSchedulesExpr
    (body childContracts contract orders : Expr) : MetaM Expr := do
  let (ruleNameType, _ruleNames) ← ruleNamesValues contract
  let names? ← try pure (some (← exprList _ruleNames)) catch _ => pure none
  if names?.isNone then
    return ← deriveSymbolicRuleSchedulesExpr
      body childContracts contract orders ruleNameType
  let names := names?.get!
  let outputValue ← withLocalDeclD `name ruleNameType fun name => do
    let scheduleType ← mkAppM ``OutputSchedule
      #[body, childContracts, contract, name]
    mkLambdaFVars #[name] scheduleType
  let mut outputCertificates := mkAppN
    (mkConst ``DependentList.nil [.zero, .succ .zero]) #[ruleNameType, outputValue]
  let mut outputKeys := mkApp (mkConst ``List.nil [.zero]) ruleNameType
  let mut outputOrders : List (List Expr) := []
  let mut outputSchedules : List Expr := []
  let mut containsFamily := false
  for name in names.reverse do
    let ordered ← mkAppM ``ScheduleDerivation.RuleScheduleOrders.output #[orders, name]
    let steps ← orderSteps ordered
    let calls := steps.filterMap fun
      | .call occurrence => some occurrence
      | .family .. => none
    if steps.any fun | .family .. => true | .call _ => false then
      containsFamily := true
    let scheduleType ← mkAppM ``OutputSchedule
      #[body, childContracts, contract, name]
    let schedule ← deriveScheduleExpr scheduleType ordered
    outputCertificates := mkAppN (mkConst ``DependentList.cons [.zero, .succ .zero])
      #[ruleNameType, outputValue, name, outputKeys, schedule, outputCertificates]
    outputKeys := mkApp3 (mkConst ``List.cons [.zero]) ruleNameType name outputKeys
    outputOrders := calls :: outputOrders
    outputSchedules := schedule :: outputSchedules
  let outputFunction := mkAppN
    (mkConst ``ScheduleDerivation.outputSchedulesFromCertificates)
    #[body, childContracts, contract, outputCertificates]
  let stateOrderExpr ← mkAppM ``ScheduleDerivation.RuleScheduleOrders.state #[orders]
  let stateSteps ← orderSteps stateOrderExpr
  let stateOrder := stateSteps.filterMap fun
    | .call occurrence => some occurrence
      | .family .. => none
  if stateSteps.any fun | .family .. => true | .call _ => false then
    containsFamily := true
  let stateType ← mkAppM ``StateSchedule #[body, childContracts]
  let stateSchedule ← deriveScheduleExpr stateType stateOrderExpr
  let schedules := mkAppN (mkConst ``RuleSchedules.mk)
    #[body, childContracts, contract, outputFunction, stateSchedule]
  let coverage ← if containsFamily then
      (buildCoverageByTactic orders schedules stateSchedule outputCertificates
        _ruleNames names outputSchedules)
    else
      try
        buildCoverageProof body childContracts schedules stateSchedule
          stateOrder names outputOrders outputSchedules
      catch _ =>
        (buildCoverageByTactic orders schedules stateSchedule outputCertificates
          _ruleNames names outputSchedules)
  pure <| mkAppN (mkConst ``ScheduleDerivation.DerivedRuleSchedules.mk)
    #[body, childContracts, contract, schedules, coverage]

elab_rules : tactic
  | `(tactic| derive_schedule $orderedSyntax) => do
      let goal ← getMainGoal
      goal.withContext do
        let target ← goal.getType
        let reducedTarget ← withTransparency .reducible <| whnf target
        let (_, targetArgs) := reducedTarget.getAppFnArgs
        unless reducedTarget.getAppFn.constName? == some ``Schedule &&
            targetArgs.size == 5 do
          throwError "`derive_schedule` expects an output or state schedule goal"
        let body ← withTransparency .reducible <| whnf targetArgs[0]!
        let childContracts ← withTransparency .reducible <| whnf targetArgs[1]!
        let occurrenceType ← mkAppM ``RuleOccurrence #[body, childContracts]
        let orderedType := mkApp (mkConst ``List [.zero]) occurrenceType
        let ordered ← Term.elabTerm orderedSyntax (some orderedType)
        Term.synthesizeSyntheticMVarsNoPostponing
        let ordered ← instantiateMVars ordered
        let schedule ← deriveScheduleExpr target ordered
        goal.assign schedule
        replaceMainGoal []
  | `(tactic| derive_complete_schedule $orderedSyntax) => do
      let goal ← getMainGoal
      goal.withContext do
        let target ← withTransparency .reducible <| whnf (← goal.getType)
        let (targetName, targetArgs) := target.getAppFnArgs
        unless targetName == ``ScheduleDerivation.DerivedCompleteSchedule &&
            targetArgs.size == 2 do
          throwError
            "`derive_complete_schedule` expects a `DerivedCompleteSchedule` goal"
        let body ← withTransparency .reducible <| whnf targetArgs[0]!
        let childContracts ← withTransparency .reducible <| whnf targetArgs[1]!
        let occurrenceType ← mkAppM ``RuleOccurrence #[body, childContracts]
        let orderedType := mkApp (mkConst ``List [.zero]) occurrenceType
        let ordered ← Term.elabTerm orderedSyntax (some orderedType)
        Term.synthesizeSyntheticMVarsNoPostponing
        let ordered ← instantiateMVars ordered
        let result ← deriveCompleteScheduleExpr target ordered
        goal.assign result
        replaceMainGoal []
  | `(tactic| derive_rule_schedules $ordersSyntax) => do
      let goal ← getMainGoal
      goal.withContext do
        let target ← withTransparency .reducible <| whnf (← goal.getType)
        let (targetName, targetArgs) := target.getAppFnArgs
        unless targetName == ``ScheduleDerivation.DerivedRuleSchedules &&
            targetArgs.size == 3 do
          throwError "`derive_rule_schedules` expects a `DerivedRuleSchedules` goal"
        let body := targetArgs[0]!
        let childContracts := targetArgs[1]!
        let contract := targetArgs[2]!
        let ordersType ← mkAppM ``ScheduleDerivation.RuleScheduleOrders
          #[body, childContracts, contract]
        let orders ← Term.elabTerm ordersSyntax (some ordersType)
        Term.synthesizeSyntheticMVarsNoPostponing
        let orders ← instantiateMVars orders
        let result ← deriveRuleSchedulesExpr body childContracts contract orders
        goal.assign result
        replaceMainGoal []

end Silean.Contracts.Cycle.Certification.Layer
