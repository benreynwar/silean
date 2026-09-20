import Silean.Contracts.Cycle.CycleLayerExistence

namespace Silean.Contracts.Cycle.Certification.Layer

open Silean

/-- The contract-state type of one certified child. Keeping `children` as an
argument lets Lean recover the otherwise implicit child-contract family in
small parent-proof helpers. -/
@[reducible] def ChildStructures.ContractState
    (_children : ChildStructures body childContracts)
    (child : body.instancePorts.Name) : Type :=
  (childContracts child).state.Values

/-! Small congruence lemmas used when composing typed child-output equations.
They avoid rewriting through the dependent child-output family itself. -/

theorem apply₂_congr {α β γ : Type} (function : α → β → γ)
    {left left' : α} {right right' : β}
    (leftEq : left = left') (rightEq : right = right') :
    function left right = function left' right' := by
  subst left'
  subst right'
  rfl

theorem bif_congr {α : Type} {select select' : Bool}
    {whenTrue whenTrue' whenFalse whenFalse' : α}
    (selectEq : select = select') (whenTrueEq : whenTrue = whenTrue')
    (whenFalseEq : whenFalse = whenFalse') :
    (bif select then whenTrue else whenFalse) =
      bif select' then whenTrue' else whenFalse' := by
  subst select'
  subst whenTrue'
  subst whenFalse'
  rfl

/-- The contract boundary step induced by one child assignment. The next
contract state is canonical because a cycle contract's state rule is
deterministic. Naming this step keeps dependent child proofs from exposing a
large inline record expression. -/
@[reducible] def childContractStep
    (children : ChildStructures body childContracts)
    (hierStep : HierStep (moduleStructure body children))
    (child : body.instancePorts.Name)
    (contractState : (childContracts child).state.Values) :
    (childContracts child).Step :=
  { inputs := body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs child
    currentState := contractState
    outputs := hierStep.childOutputs child
    nextState := (childContracts child).stateRule.apply
      (body.wiring.childInputValues hierStep.inputs
        hierStep.childOutputs child) contractState }

@[simp] theorem childContractStep_inputs
    (children : ChildStructures body childContracts)
    (hierStep : HierStep (moduleStructure body children))
    (child : body.instancePorts.Name)
    (contractState : (childContracts child).state.Values) :
    (childContractStep children hierStep child contractState).inputs =
      body.wiring.childInputValues hierStep.inputs hierStep.childOutputs child :=
  rfl

@[simp] theorem childContractStep_outputs
    (children : ChildStructures body childContracts)
    (hierStep : HierStep (moduleStructure body children))
    (child : body.instancePorts.Name)
    (contractState : (childContracts child).state.Values) :
    (childContractStep children hierStep child contractState).outputs =
      hierStep.childOutputs child :=
  rfl

/-- The result of applying a certified child's public contract to its part of
the parent's structural solution. Parent proofs normally use `ruleHolds`;
`allowed` exposes the complete Step fact when a theorem needs the whole child
transition, and `nextCorresponds` threads state correspondence forward. -/
structure ChildContractMatch
    (children : ChildStructures body childContracts)
    (hierStep : HierStep (moduleStructure body children))
    (child : body.instancePorts.Name)
    (contractState : (childContracts child).state.Values) : Prop where
  allowed : (childContracts child).Allows
    (childContractStep children hierStep child contractState)
  nextCorresponds : (children child).certification.stateCorresponds
    ((childContracts child).stateRule.apply
      (body.wiring.childInputValues hierStep.inputs
        hierStep.childOutputs child) contractState)
    (HierStep.nextState (children child).moduleStructure
      (hierStep.children child))

/-- The common parent-proof view of a child match: a named output rule holds
for the child inputs and outputs induced by the hierarchy assignment. -/
theorem ChildContractMatch.ruleHolds
    {body : ModuleBody}
    {childContracts : ChildCycleContracts body}
    {children : ChildStructures body childContracts}
    {hierStep : HierStep (moduleStructure body children)}
    {child : body.instancePorts.Name}
    {contractState : (childContracts child).state.Values}
    (childMatch : ChildContractMatch children hierStep child contractState)
    (rule : (childContracts child).RuleName) :
    ((childContracts child).outputRule rule).Holds
      (body.wiring.childInputValues hierStep.inputs
        hierStep.childOutputs child)
      contractState
      (hierStep.childOutputs child) := by
  exact childMatch.allowed.1 rule

/-- Apply one contract-derived output equation directly at a child's visible
boundary. The equation may depend on the child's contract state, but does not
expose the synthetic `childContractStep` used to instantiate it. -/
theorem ChildContractMatch.boundaryOutput
    {body : ModuleBody}
    {childContracts : ChildCycleContracts body}
    {children : ChildStructures body childContracts}
    {hierStep : HierStep (moduleStructure body children)}
    {child : body.instancePorts.Name}
    {contractState : (childContracts child).state.Values}
    (childMatch : ChildContractMatch children hierStep child contractState)
    {output : (body.instancePorts.ports child).outputs.Label}
    (equation : (childContracts child).OutputEquation output) :
    (hierStep.childOutputs child) output =
      equation.target
        (body.wiring.childInputValues hierStep.inputs
          hierStep.childOutputs child)
        contractState := by
  exact equation.holds childMatch.allowed

/-- Apply a child's public boundary theorem without exposing the internal Step
used to connect the child's contract to the parent's structural assignment.
This presents contract-derived output facts directly over the child inputs and
outputs visible in the parent proof. -/
theorem ChildContractMatch.boundaryFact
    {body : ModuleBody}
    {childContracts : ChildCycleContracts body}
    {children : ChildStructures body childContracts}
    {hierStep : HierStep (moduleStructure body children)}
    {child : body.instancePorts.Name}
    {contractState : (childContracts child).state.Values}
    (childMatch : ChildContractMatch children hierStep child contractState)
    {property :
      (body.instancePorts.ports child).inputs.Values →
        (body.instancePorts.ports child).outputs.Values → Prop}
    (ofAllowed : ∀ {step : (childContracts child).Step},
      (childContracts child).Allows step → property step.inputs step.outputs) :
    property
      (body.wiring.childInputValues hierStep.inputs
        hierStep.childOutputs child)
      (hierStep.childOutputs child) := by
  exact ofAllowed childMatch.allowed

/-- Apply one child's public contract to its part of a valid layer solution.
The result depends only on the declared contract and supplied certification,
not on any schedule or definition internal to the child. -/
theorem childSolutionMatchesContract
    (children : ChildStructures body childContracts)
    (hierStep : HierStep (moduleStructure body children))
    (satisfies : (moduleStructure body children).IsSolution hierStep)
    (child : body.instancePorts.Name)
    (contractState : (childContracts child).state.Values)
    (corresponds : (children child).certification.stateCorresponds contractState
      (HierStep.currentState (children child).moduleStructure
        (hierStep.children child))) :
    ChildContractMatch children hierStep child contractState := by
  rcases (children child).certification.implements contractState
      (hierStep.children child).step corresponds
      (ModuleStructure.child_realizes satisfies child) with
    ⟨nextState, allowed, nextCorresponds⟩
  change (childContracts child).OutputRulesHold
      (hierStep.children child).inputs contractState
      (hierStep.children child).outputs ∧
    nextState = (childContracts child).stateRule.apply
      (hierStep.children child).inputs contractState at allowed
  change (children child).certification.stateCorresponds
    nextState (HierStep.nextState (children child).moduleStructure
      (hierStep.children child)) at nextCorresponds
  have childInputsEqual := satisfies.2.1 child
  change (hierStep.children child).inputs =
    body.wiring.childInputValues hierStep.inputs hierStep.childOutputs child
    at childInputsEqual
  rw [childInputsEqual] at allowed
  rw [allowed.2] at nextCorresponds
  exact ⟨⟨allowed.1, rfl⟩, nextCorresponds⟩

/-- Apply a child's contract using a contract state supplied by that child's
state-coverage theorem. This is the natural parent-proof interface when only
the child's boundary behavior matters; parents that relate a particular
contract state should use `childSolutionMatchesContract` directly. -/
theorem childSolutionMatchesCoveredContract
    (children : ChildStructures body childContracts)
    (hierStep : HierStep (moduleStructure body children))
    (satisfies : (moduleStructure body children).IsSolution hierStep)
    (child : body.instancePorts.Name) :
    ∃ contractState, ChildContractMatch children hierStep child contractState := by
  rcases (children child).certification.hasCorrespondingState
      (HierStep.currentState (children child).moduleStructure
        (hierStep.children child)) with ⟨contractState, corresponds⟩
  exact ⟨contractState, childSolutionMatchesContract children hierStep satisfies
    child contractState corresponds⟩

/-- For a stateless child, state coverage supplies the correspondence witness
automatically, so a parent can use the public child contract directly. -/
theorem childSolutionMatchesContract_of_subsingletonState
    (children : ChildStructures body childContracts)
    (hierStep : HierStep (moduleStructure body children))
    (satisfies : (moduleStructure body children).IsSolution hierStep)
    (child : body.instancePorts.Name)
    [Subsingleton (childContracts child).state.Values]
    (contractState : (childContracts child).state.Values) :
    ChildContractMatch children hierStep child contractState := by
  rcases (children child).certification.hasCorrespondingState
      (HierStep.currentState (children child).moduleStructure
        (hierStep.children child)) with ⟨coveredState, covered⟩
  have corresponds : (children child).certification.stateCorresponds contractState
      (HierStep.currentState (children child).moduleStructure
        (hierStep.children child)) := by
    rw [Subsingleton.elim contractState coveredState]
    exact covered
  exact childSolutionMatchesContract children hierStep satisfies child
    contractState corresponds

/-- Apply every stateless child's contract at once. A module supplies the
unique state value for each child; the helper handles correspondence coverage
and returns a dependent family of child-contract matches. -/
theorem childSolutionsMatchContracts_of_subsingletonState
    (children : ChildStructures body childContracts)
    (hierStep : HierStep (moduleStructure body children))
    (satisfies : (moduleStructure body children).IsSolution hierStep)
    (contractStates : (child : body.instancePorts.Name) →
      (childContracts child).state.Values)
    (stateSubsingleton : ∀ child,
      Subsingleton (childContracts child).state.Values) :
    ∀ child,
      ChildContractMatch children hierStep child (contractStates child) := by
  intro child
  letI := stateSubsingleton child
  exact childSolutionMatchesContract_of_subsingletonState children hierStep
    satisfies child (contractStates child)

/-! ## Assembling a scheduled layer certificate

The schedules and their coverage proof establish the two generic structural
facts required by every non-blackbox layer: a solution exists and is unique.
A module still supplies its state correspondence and the meaningful proof that
every structural solution implements its contract.  Keeping this constructor
here prevents module files from repeatedly rebuilding the same certification
record, without making schedules part of either the structure or its public
certificate.

Recursive module families use this same constructor for each structural layer;
their separate recursion is only responsible for choosing and instantiating
the certified child structures. -/

/-- Build a certified structural layer from complete rule schedules and the
module-specific behavioral evidence. -/
noncomputable def RuleSchedules.certifiedLayer
    {body : ModuleBody}
    {childContracts : ChildCycleContracts body}
    {cycleContract : ModuleCycleContract body.ports}
    (schedules : RuleSchedules body childContracts cycleContract)
    (covers : schedules.CoversChildren)
    (stateCorresponds :
      (children : ChildStructures body childContracts) →
        cycleContract.state.Values → (moduleStructure body children).State → Prop)
    (hasCorrespondingState :
      (children : ChildStructures body childContracts) →
      ∀ structuralState, ∃ contractState,
        stateCorresponds children contractState structuralState)
    (implements :
      (children : ChildStructures body childContracts) →
        ImplementsSolutions (moduleStructure body children) cycleContract
          (stateCorresponds children)) :
    ModuleCycleCertifiedLayer body childContracts cycleContract where
  certify children := {
    stateCorresponds := stateCorresponds children
    hasCorrespondingState := hasCorrespondingState children
    hasStructuralResult := schedules.hasSolution covers children
    structuralResultUnique := schedules.hasAtMostOneSolution covers children
    implements := implementsSolutions_iff_implements.mp (implements children)
  }

/-! Parent proofs often specialize a public child-contract theorem and then
normalize the child inputs induced by the parent's wiring. These tactics keep
that mechanical normalization concise without exposing child implementations. -/

syntax (name := normalizeChildContract)
  "normalize_child_contract " term : tactic

syntax (name := normalizeChildHyp)
  "normalize_child_hyp " Lean.Parser.Tactic.locationHyp : tactic

syntax (name := normalizeCompositeChildHyp)
  "normalize_child_hyp " Lean.Parser.Tactic.locationHyp " unfolding "
    term ", " term : tactic

/-- Introduce a dependent family of contract matches for children whose
contract states are all definitionally the empty signal map.  The resulting
fact uses only the supplied child certifications and structural-solution
hypothesis. -/
syntax (name := deriveEmptyStateChildMatches)
  "derive_empty_state_child_matches " ident " for " term " from " term ", "
    term ", " term : tactic

/-- Introduce the contract match for one child whose contract state is
definitionally `emptySignalMap`. Supplying the canonical empty value both
checks that condition and lets Lean infer the required `Subsingleton`
instance. -/
syntax (name := deriveEmptyStateChildMatch)
  "derive_empty_state_child_match " ident " for " term " in " term " from "
    term ", " term ", " term : tactic

/-- Introduce a named fact by applying a public child-contract theorem to
allowed-step evidence and normalizing the inputs induced by the parent wiring. -/
syntax (name := childContractFact)
  "child_contract_fact " ident " : " term " from " term " using " term : tactic

syntax (name := compositeChildContractFact)
  "child_contract_fact " ident " : " term " from " term " using " term
    " unfolding " term ", " term ", " term : tactic

macro_rules
  | `(tactic| normalize_child_contract $proof:term) =>
      `(tactic| simpa only [childContractStep_inputs, childContractStep_outputs,
        Wiring.childInputValues,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using $proof)
  | `(tactic| normalize_child_hyp $hyp:locationHyp unfolding
        $wiring:term, $context:term) =>
      `(tactic| dsimp only [childContractStep_inputs, childContractStep_outputs,
        Wiring.childInputValues,
        $wiring:term, $context:term,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] at $hyp)
  | `(tactic| normalize_child_hyp $hyp:locationHyp) =>
      `(tactic| simp only [childContractStep_inputs, childContractStep_outputs,
        Wiring.childInputValues,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] at $hyp)
  | `(tactic| derive_empty_state_child_matches $name:ident for $body:term from
        $children:term, $hierStep:term, $satisfies:term) =>
      `(tactic|
        have $name :=
          childSolutionsMatchContracts_of_subsingletonState
            (body := $body) $children $hierStep $satisfies
            (fun child => by cases child <;> exact SignalMap.emptyValues)
            (fun child => by
              cases child <;>
                change Subsingleton emptySignalMap.Values <;>
                infer_instance))
  | `(tactic| derive_empty_state_child_match $name:ident for $child:term in
        $body:term from $children:term, $hierStep:term, $satisfies:term) =>
      `(tactic|
        have $name := by
          letI : Subsingleton
              (ChildStructures.ContractState $children $child) := by
            change Subsingleton emptySignalMap.Values
            infer_instance
          exact childSolutionMatchesContract_of_subsingletonState
              (body := $body) $children $hierStep $satisfies $child
              SignalMap.emptyValues)
  | `(tactic| child_contract_fact $name:ident : $type:term from
        $allowed:term using $contractTheorem:term) =>
      `(tactic|
        have $name : $type := by
          normalize_child_contract ($contractTheorem $allowed))
  | `(tactic| child_contract_fact $name:ident : $type:term from
        $allowed:term using $contractTheorem:term unfolding
        $body:term, $wiring:term, $endpointContext:term) =>
      `(tactic|
        have $name : $type := by
          have normalized := $contractTheorem $allowed
          dsimp only [childContractStep_inputs, childContractStep_outputs,
            Wiring.childInputValues,
            $body:term, $wiring:term, $endpointContext:term,
            EndpointContext.moduleInput, EndpointContext.instanceOutput,
            SignalSource.value] at normalized
          exact normalized)

end Silean.Contracts.Cycle.Certification.Layer
