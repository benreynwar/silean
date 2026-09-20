import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Contracts.Cycle.CycleImplementation

/-! # Contracts for authored circuit descriptions

An authored description does not need a second hardware semantics.  Correctness
instead quantifies over ordinary production structures whose naming is proven
to `Corresponds` to the description.  Generated code later supplies one such
structure and its correspondence proof.
-/

namespace Silean.Authoring.CircuitDescription

open Silean Naming

namespace Description

/-- A typed composite body whose parent boundary is fixed while its generated
child-label type and wiring remain abstract. -/
structure Body (ports : ModulePorts) where
  instancePorts : InstancePorts
  wiring : Wiring ports instancePorts

namespace Body

@[reducible] def moduleBody (body : Body ports) : ModuleBody where
  context := ⟨ports, body.instancePorts⟩
  wiring := body.wiring

end Body

/-- Any ordinary typed composite that has the requested boundary naming and is
proven to be the same named circuit as `description`. -/
structure Realization (description : Description) (ports : ModulePorts)
    (boundaryNaming : ModulePortsNaming ports) where
  body : Body ports
  children : (child : body.instancePorts.Name) →
    ModuleStructure (body.instancePorts.ports child)
  key : ModuleKey
  instanceName : body.instancePorts.Name → SourceName
  childNaming : (child : body.instancePorts.Name) → ModuleNaming (children child)
  namedWires : List (Naming.NamedWire body.moduleBody) := []
  corresponds : Corresponds description
    (.composite key boundaryNaming instanceName childNaming namedWires)

namespace Realization

@[reducible] def moduleStructure
    (realization : Realization description ports boundaryNaming) :
    ModuleStructure ports :=
  .composite realization.body.moduleBody realization.children

@[reducible] def naming
    (realization : Realization description ports boundaryNaming) :
    ModuleNaming realization.moduleStructure :=
  .composite realization.key boundaryNaming realization.instanceName
    realization.childNaming realization.namedWires

end Realization

/-- Every production structure corresponding to the authored construction
implements the contract.  The existential relation hides how behavioral state
is represented by a particular generated hierarchy; coverage rules out a
vacuous relation. -/
def ImplementsCycleContract (description : Description)
    (contract : Contracts.Cycle.ModuleCycleContract ports)
    (boundaryNaming : ModulePortsNaming ports) : Prop :=
  ∀ realization : Realization description ports boundaryNaming,
    ∃ stateCorresponds : contract.state.Values →
        realization.moduleStructure.State → Prop,
      (∀ structuralState, ∃ contractState,
        stateCorresponds contractState structuralState) ∧
      Contracts.Cycle.ImplementsSolutions realization.moduleStructure contract
        stateCorresponds

namespace ImplementsCycleContract

/-- One certified reference realization proves the implementation-independent
claim. Correspondence transports complete hierarchy solutions and structural
state, keeping generated labels and transport proofs out of module-specific
code. -/
theorem of_certification
    {ports : ModulePorts}
    {description : Description}
    {contract : Contracts.Cycle.ModuleCycleContract ports}
    {boundaryNaming : ModulePortsNaming ports}
    {referenceBody : Body ports}
    {children : (child : referenceBody.instancePorts.Name) →
      ModuleStructure (referenceBody.instancePorts.ports child)}
    {key : ModuleKey}
    {instanceName : referenceBody.instancePorts.Name → SourceName}
    {childNaming : (child : referenceBody.instancePorts.Name) →
      ModuleNaming (children child)}
    {namedWires : List (Naming.NamedWire referenceBody.moduleBody)}
    (referenceCorresponds : Corresponds description
      (.composite key boundaryNaming instanceName childNaming namedWires))
    (certification : Contracts.Cycle.ModuleCycleCertification
      (.composite referenceBody.moduleBody children) contract) :
    ImplementsCycleContract description contract boundaryNaming := by
  intro implementation
  refine ⟨fun contractState structuralState =>
    certification.stateCorresponds contractState
      ((implementation.corresponds.childBijection referenceCorresponds).transfer
        (fun entry => entry.module.moduleStructure.State) structuralState), ?_, ?_⟩
  · intro structuralState
    obtain ⟨contractState, corresponds⟩ := certification.hasCorrespondingState
      ((implementation.corresponds.childBijection referenceCorresponds).transfer
        (fun entry => entry.module.moduleStructure.State) structuralState)
    exact ⟨contractState, corresponds⟩
  · intro contractState step stateCorresponds solution
    let referenceStep := implementation.corresponds.transferHierStep
      referenceCorresponds step
    have referenceSolution :=
      (implementation.corresponds.transferSolution_iff
        referenceCorresponds step).mp solution
    have referenceStateEqual :
        (implementation.corresponds.childBijection referenceCorresponds).transfer
          (fun entry => entry.module.moduleStructure.State) step.currentState =
          referenceStep.currentState :=
      implementation.corresponds.transferCurrentState referenceCorresponds step
    rw [referenceStateEqual] at stateCorresponds
    have referenceImplements :=
      Contracts.Cycle.implementsSolutions_iff_implements.mpr
        certification.implements
    obtain ⟨nextContractState, allowed, nextCorresponds⟩ :=
      referenceImplements contractState referenceStep stateCorresponds
        referenceSolution
    have inputsEqual : referenceStep.inputs = step.inputs := by
      funext port
      exact (eq_of_heq (implementation.corresponds.transferInputs_agree
        referenceCorresponds step.inputs port port rfl)).symm
    have outputsEqual : referenceStep.outputs = step.outputs := by
      funext port
      exact (eq_of_heq (implementation.corresponds.transferOutputs_agree
        referenceCorresponds step port port rfl)).symm
    refine ⟨nextContractState, ?_, ?_⟩
    · rw [← inputsEqual, ← outputsEqual]
      exact allowed
    · have nextStateEqual :
          (implementation.corresponds.childBijection referenceCorresponds).transfer
            (fun entry => entry.module.moduleStructure.State) step.nextState =
            referenceStep.nextState :=
        implementation.corresponds.transferNextState referenceCorresponds step
      change certification.stateCorresponds nextContractState
        ((implementation.corresponds.childBijection referenceCorresponds).transfer
          (fun entry => entry.module.moduleStructure.State) step.nextState)
      rw [nextStateEqual]
      exact nextCorresponds

end ImplementsCycleContract

end Description

end Silean.Authoring.CircuitDescription
