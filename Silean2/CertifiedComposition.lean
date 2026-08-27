import Silean2.ModuleCycleCertified

namespace Silean2.Certified

open Silean2

/-! A parent reasons about each child only through its certified contract. The
child structure is recovered from that certificate; none of the child's local
schedules appear in this interface. -/

abbrev Children (body : ModuleBody) :=
  (name : body.context.instances.Name) →
    ModuleCycleCertified (body.context.instances.ports name)

@[reducible] def childStructure (children : Children body)
    (name : body.context.instances.Name) :=
  (children name).moduleStructure

@[reducible] def moduleStructure (body : ModuleBody) (children : Children body) :
    ModuleStructure body.context.ports :=
  .composite body (childStructure children)

/-! Apply one child's behavioral certificate to its part of a valid composite
proposal. The child's inputs are the ones induced by the parent wiring; no
schedule or child implementation detail crosses this boundary. -/

theorem childImplements {body : ModuleBody} (children : Children body)
    (inputs : body.context.ports.inputs.Values)
    (structuralState : (moduleStructure body children).State)
    (proposal : ProposedValues (moduleStructure body children))
    (satisfies : (moduleStructure body children).IsSolution
      inputs structuralState proposal)
    (child : body.context.instances.Name)
    (contractState : (children child).cycleContract.state.Values)
    (corresponds : (children child).stateCorresponds contractState
      (structuralState child)) :
    ∃ nextContractState,
      (children child).cycleContract.EvaluatesTo
        (ProposedValues.childInputs body (childStructure children)
          inputs proposal.2 child)
        contractState (proposal.2 child).outputs nextContractState ∧
      (children child).stateCorresponds nextContractState
        (proposal.2 child).nextState :=
  (children child).implements
    (ProposedValues.childInputs body (childStructure children)
      inputs proposal.2 child)
    contractState (structuralState child) (proposal.2 child)
    corresponds (satisfies.2 child)

/-- The normalized form of `childImplements`: a parent gets the child's public
output equations and next-state correspondence with no existential next-state
name or rewrite step. -/
theorem childSolutionMatchesContract {body : ModuleBody} (children : Children body)
    (inputs : body.context.ports.inputs.Values)
    (structuralState : (moduleStructure body children).State)
    (proposal : ProposedValues (moduleStructure body children))
    (satisfies : (moduleStructure body children).IsSolution
      inputs structuralState proposal)
    (child : body.context.instances.Name)
    (contractState : (children child).cycleContract.state.Values)
    (corresponds : (children child).stateCorresponds contractState
      (structuralState child)) :
    (children child).cycleContract.EvaluatesTo
        (ProposedValues.childInputs body (childStructure children)
          inputs proposal.2 child)
        contractState (proposal.2 child).outputs
        ((children child).cycleContract.stateRule.apply
          (ProposedValues.childInputs body (childStructure children)
            inputs proposal.2 child)
          contractState) ∧
      (children child).stateCorresponds
        ((children child).cycleContract.stateRule.apply
          (ProposedValues.childInputs body (childStructure children)
            inputs proposal.2 child)
          contractState)
        (proposal.2 child).nextState := by
  rcases childImplements children inputs structuralState proposal satisfies child
      contractState corresponds with
    ⟨nextState, evaluates, nextCorresponds⟩
  rw [evaluates.2] at nextCorresponds
  exact ⟨⟨evaluates.1, rfl⟩, nextCorresponds⟩

end Silean2.Certified
