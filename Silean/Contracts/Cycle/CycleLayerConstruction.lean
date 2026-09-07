import Silean.Contracts.Cycle.CycleLayerExistence

namespace Silean.Contracts.Cycle.Certification.Layer

open Silean

/-- Apply one child's public contract to its part of a valid layer solution.
The result depends only on the declared contract and supplied certification,
not on any schedule or definition internal to the child. -/
theorem childSolutionMatchesContract
    (children : ChildStructures body childContracts)
    (inputs : body.ports.inputs.Values)
    (structuralState : (moduleStructure body children).State)
    (proposal : ProposedValues (moduleStructure body children))
    (satisfies : (moduleStructure body children).IsSolution
      inputs structuralState proposal)
    (child : body.instancePorts.Name)
    (contractState : (childContracts child).state.Values)
    (corresponds : (children child).certification.stateCorresponds contractState
      (structuralState child)) :
    (childContracts child).EvaluatesTo
        (ProposedValues.childInputs body
          (fun name => (children name).moduleStructure)
          inputs proposal.2 child)
        contractState (proposal.2 child).outputs
        ((childContracts child).stateRule.apply
          (ProposedValues.childInputs body
            (fun name => (children name).moduleStructure)
            inputs proposal.2 child)
          contractState) ∧
      (children child).certification.stateCorresponds
        ((childContracts child).stateRule.apply
          (ProposedValues.childInputs body
            (fun name => (children name).moduleStructure)
            inputs proposal.2 child)
          contractState)
        (proposal.2 child).nextState := by
  rcases (children child).certification.implements
      (ProposedValues.childInputs body
        (fun name => (children name).moduleStructure)
        inputs proposal.2 child)
      contractState (structuralState child) (proposal.2 child)
      corresponds (satisfies.2 child) with
    ⟨nextState, evaluates, nextCorresponds⟩
  rw [evaluates.2] at nextCorresponds
  exact ⟨⟨evaluates.1, rfl⟩, nextCorresponds⟩

/-- For a stateless child, state coverage supplies the correspondence witness
automatically, so a parent can use the public child contract directly. -/
theorem childSolutionMatchesContract_of_subsingletonState
    (children : ChildStructures body childContracts)
    (inputs : body.ports.inputs.Values)
    (structuralState : (moduleStructure body children).State)
    (proposal : ProposedValues (moduleStructure body children))
    (satisfies : (moduleStructure body children).IsSolution
      inputs structuralState proposal)
    (child : body.instancePorts.Name)
    [Subsingleton (childContracts child).state.Values]
    (contractState : (childContracts child).state.Values) :
    (childContracts child).EvaluatesTo
        (ProposedValues.childInputs body
          (fun name => (children name).moduleStructure)
          inputs proposal.2 child)
        contractState (proposal.2 child).outputs
        ((childContracts child).stateRule.apply
          (ProposedValues.childInputs body
            (fun name => (children name).moduleStructure)
            inputs proposal.2 child)
          contractState) ∧
      (children child).certification.stateCorresponds
        ((childContracts child).stateRule.apply
          (ProposedValues.childInputs body
            (fun name => (children name).moduleStructure)
            inputs proposal.2 child)
          contractState)
        (proposal.2 child).nextState := by
  rcases (children child).certification.hasCorrespondingState
      (structuralState child) with ⟨coveredState, covered⟩
  have corresponds : (children child).certification.stateCorresponds contractState
      (structuralState child) := by
    rw [Subsingleton.elim contractState coveredState]
    exact covered
  exact childSolutionMatchesContract children inputs structuralState proposal
    satisfies child contractState corresponds

/-- Apply every stateless child's contract at once. A module supplies the
unique state value for each child; the helper handles correspondence coverage
and returns a dependent family of contract evaluations. -/
theorem childSolutionsMatchContracts_of_subsingletonState
    (children : ChildStructures body childContracts)
    (inputs : body.ports.inputs.Values)
    (structuralState : (moduleStructure body children).State)
    (proposal : ProposedValues (moduleStructure body children))
    (satisfies : (moduleStructure body children).IsSolution
      inputs structuralState proposal)
    (contractStates : (child : body.instancePorts.Name) →
      (childContracts child).state.Values)
    (stateSubsingleton : ∀ child,
      Subsingleton (childContracts child).state.Values) :
    ∀ child,
      (childContracts child).EvaluatesTo
          (ProposedValues.childInputs body
            (fun name => (children name).moduleStructure)
            inputs proposal.2 child)
          (contractStates child) (proposal.2 child).outputs
          ((childContracts child).stateRule.apply
            (ProposedValues.childInputs body
              (fun name => (children name).moduleStructure)
              inputs proposal.2 child)
            (contractStates child)) ∧
        (children child).certification.stateCorresponds
          ((childContracts child).stateRule.apply
            (ProposedValues.childInputs body
              (fun name => (children name).moduleStructure)
              inputs proposal.2 child)
            (contractStates child))
          (proposal.2 child).nextState := by
  intro child
  letI := stateSubsingleton child
  exact childSolutionMatchesContract_of_subsingletonState children inputs
    structuralState proposal satisfies child (contractStates child)

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
        Implements (moduleStructure body children) cycleContract
          (stateCorresponds children)) :
    ModuleCycleCertifiedLayer body childContracts cycleContract where
  certify children := {
    stateCorresponds := stateCorresponds children
    hasCorrespondingState := hasCorrespondingState children
    hasStructuralResult := schedules.hasSolution covers children
    structuralResultUnique := schedules.hasAtMostOneSolution covers children
    implements := implements children
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
    Lean.Parser.Tactic.simpArg ", " Lean.Parser.Tactic.simpArg ", "
    Lean.Parser.Tactic.simpArg : tactic

/-- Introduce a dependent family of contract evaluations for children whose
contract states are all definitionally the empty signal map.  The resulting
fact uses only the supplied child certifications and structural-solution
hypothesis. -/
syntax (name := deriveEmptyStateChildMatches)
  "derive_empty_state_child_matches " ident " from " term ", " term ", "
    term ", " term ", " term : tactic

/-- Introduce a named fact by applying a public child-contract theorem to a
child evaluation and normalizing the inputs induced by the parent wiring. -/
syntax (name := childContractFact)
  "child_contract_fact " ident " : " term " from " term " using " term : tactic

syntax (name := compositeChildContractFact)
  "child_contract_fact " ident " : " term " from " term " using " term
    " unfolding " Lean.Parser.Tactic.simpArg ", " Lean.Parser.Tactic.simpArg ", "
    Lean.Parser.Tactic.simpArg : tactic

macro_rules
  | `(tactic| normalize_child_contract $proof:term) =>
      `(tactic| simpa [ProposedValues.childInputs_apply,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using $proof)
  | `(tactic| normalize_child_hyp $hyp:locationHyp unfolding
        $body, $wiring, $context) =>
      `(tactic| simp only [ProposedValues.childInputs_apply,
        $body, $wiring, $context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] at $hyp)
  | `(tactic| normalize_child_hyp $hyp:locationHyp) =>
      `(tactic| simp only [ProposedValues.childInputs_apply,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] at $hyp)
  | `(tactic| derive_empty_state_child_matches $name:ident from
        $children:term, $inputs:term, $structuralState:term,
        $proposal:term, $satisfies:term) =>
      `(tactic|
        have $name :=
          childSolutionsMatchContracts_of_subsingletonState
            $children $inputs $structuralState $proposal $satisfies
            (fun child => by cases child <;> exact SignalMap.emptyValues)
            (fun child => by
              cases child <;>
                change Subsingleton emptySignalMap.Values <;>
                infer_instance))
  | `(tactic| child_contract_fact $name:ident : $type:term from
        $evaluation:term using $contractTheorem:term) =>
      `(tactic|
        have $name : $type := by
          normalize_child_contract ($contractTheorem $evaluation))
  | `(tactic| child_contract_fact $name:ident : $type:term from
        $evaluation:term using $contractTheorem:term unfolding
        $body, $wiring, $endpointContext) =>
      `(tactic|
        have $name : $type := by
          simpa only [ProposedValues.childInputs_apply,
            $body, $wiring, $endpointContext,
            EndpointContext.moduleInput, EndpointContext.instanceOutput,
            SignalSource.value] using ($contractTheorem $evaluation))

end Silean.Contracts.Cycle.Certification.Layer
