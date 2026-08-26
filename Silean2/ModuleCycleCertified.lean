import Silean2.ModuleCycleEvaluation
import Silean2.StructuralDependency

namespace Silean2

/-! A one-cycle refinement relates the contract's deliberately abstract state
to the module's recursively derived structural state. It quantifies over every
structural solution, so neither a schedule nor a chosen evaluator defines what it
means to implement a contract. -/

def Implements {ports : ModulePorts}
    (moduleStructure : ModuleStructure ports)
    (cycleContract : ModuleCycleContract ports)
    (stateCorresponds : cycleContract.state.Values →
      moduleStructure.State → Prop) : Prop :=
  ∀ inputs contractState structuralState proposal,
    stateCorresponds contractState structuralState →
    moduleStructure.IsSolution inputs structuralState proposal →
      ∃ nextContractState,
        cycleContract.EvaluatesTo inputs contractState proposal.outputs
          nextContractState ∧
        stateCorresponds nextContractState proposal.nextState

/-! A certified cycle module packages independent structure and behavior. State
coverage prevents an always-false correspondence from certifying vacuously. -/

structure ModuleCycleCertified (ports : ModulePorts) where
  moduleStructure : ModuleStructure ports
  cycleContract : ModuleCycleContract ports
  stateCorresponds : cycleContract.state.Values → moduleStructure.State → Prop
  hasCorrespondingState : ∀ structuralState,
    ∃ contractState, stateCorresponds contractState structuralState
  hasStructuralResult : ∀ inputs structuralState,
    ∃ proposal, moduleStructure.IsSolution inputs structuralState proposal
  structuralResultUnique : moduleStructure.HasAtMostOneSolution
  implements : Implements moduleStructure cycleContract stateCorresponds

namespace ModuleCycleCertified

/-! A certificate already contains exactly the two order-independent facts
needed for existence and uniqueness. No selected evaluator is required. -/

theorem hasExactlyOneStructuralResult
    (certified : ModuleCycleCertified ports)
    (inputs : ports.inputs.Values)
    (structuralState : certified.moduleStructure.State) :
    ∃ proposal,
      certified.moduleStructure.IsSolution inputs structuralState proposal ∧
      ∀ other,
        certified.moduleStructure.IsSolution inputs structuralState other →
        other = proposal := by
  rcases certified.hasStructuralResult inputs structuralState with
    ⟨proposal, satisfies⟩
  exact ⟨proposal, satisfies, fun other otherSatisfies =>
    certified.structuralResultUnique inputs structuralState other proposal
      otherSatisfies satisfies⟩

/-! Certification turns each behavioral rule into a semantic dependency fact
about the independent structure. This is the generic child-rule interface used
by parent schedules; it does not inspect the certified module's implementation. -/

def structuralRule (certified : ModuleCycleCertified ports)
    (name : certified.cycleContract.RuleName) :
    StructuralRule certified.moduleStructure := by
  let rule := (certified.cycleContract.outputRule name).2
  refine {
    reads := rule.readsInputs.labels
    writes := rule.writesOutputs.labels
    determines := ?_ }
  intro leftInputs rightInputs structuralState left right
    leftSatisfies rightSatisfies inputsAgree output outputMem
  rcases certified.hasCorrespondingState structuralState with
    ⟨contractState, corresponds⟩
  rcases certified.implements leftInputs contractState structuralState left
      corresponds leftSatisfies with
    ⟨leftNext, leftEvaluates, leftNextCorresponds⟩
  rcases certified.implements rightInputs contractState structuralState right
      corresponds rightSatisfies with
    ⟨rightNext, rightEvaluates, rightNextCorresponds⟩
  have selectedInputsEqual :
      rule.readsInputs.project leftInputs =
        rule.readsInputs.project rightInputs :=
    rule.readsInputs.project_eq_of_eq_on leftInputs rightInputs inputsAgree
  have leftHolds := leftEvaluates.1 name
  have rightHolds := rightEvaluates.1 name
  unfold CycleOutputRule.Holds at leftHolds rightHolds
  rw [selectedInputsEqual] at leftHolds
  exact SignalSelection.Matches.eq_of_mem rule.writesOutputs
    leftHolds rightHolds output outputMem

end ModuleCycleCertified

end Silean2
