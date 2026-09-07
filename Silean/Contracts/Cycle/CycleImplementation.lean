import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Semantics.StructuralDependency

namespace Silean.Contracts.Cycle

/-! # Certifying a structure against a cycle contract

Cycle certification relates the contract's deliberately behavioral state to
the module's recursively derived structural state. The correspondence need not
be equality or a computable function, but it must cover every structural state
and be preserved by every cycle.

Implementation quantifies over every solution of the structural equations, so
neither a proof schedule nor a chosen evaluator defines what it means to satisfy
the contract. Existence and uniqueness of those solutions are separate required
proofs. -/

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

/-! Correctness evidence for an already chosen structure and contract.  Keeping
these as parameters is important: executable consumers can use the structure
without evaluating this (generally noncomputable) proof object. -/

structure ModuleCycleCertification {ports : ModulePorts}
    (moduleStructure : ModuleStructure ports)
    (cycleContract : ModuleCycleContract ports) where
  /-- Relation between behavioral state and the hierarchy's physical state. -/
  stateCorresponds : cycleContract.state.Values → moduleStructure.State → Prop
  /-- Every physical state has at least one behavioral description. -/
  hasCorrespondingState : ∀ structuralState,
    ∃ contractState, stateCorresponds contractState structuralState
  /-- The structural equations have a solution for every input and state. -/
  hasStructuralResult : ∀ inputs structuralState,
    ∃ proposal, moduleStructure.IsSolution inputs structuralState proposal
  /-- The structural equations cannot have two different solutions. -/
  structuralResultUnique : moduleStructure.HasAtMostOneSolution
  /-- Every structural solution follows the contract and preserves correspondence. -/
  implements : Implements moduleStructure cycleContract stateCorresponds

/-! A certified cycle module packages independent structure and behavior. State
coverage prevents an always-false correspondence from certifying vacuously. -/

structure ModuleCycleCertified (ports : ModulePorts) where
  /-- The hardware hierarchy. -/
  moduleStructure : ModuleStructure ports
  /-- Its exact one-cycle behavior. -/
  cycleContract : ModuleCycleContract ports
  /-- Proof connecting the independent structure and contract. -/
  certification : ModuleCycleCertification moduleStructure cycleContract

/-- A complete hardware hierarchy certified against one already chosen cycle
contract. This is the child object consumed when instantiating a certified
structural layer. -/
structure ModuleCycleCertifiedStructure {ports : ModulePorts}
    (cycleContract : ModuleCycleContract ports) where
  /-- Concrete recursively instantiated hardware. -/
  moduleStructure : ModuleStructure ports
  /-- Proof that the concrete hierarchy implements the boundary contract. -/
  certification : ModuleCycleCertification moduleStructure cycleContract

namespace ModuleCycleCertified

/-- View a public certified module at its already bundled contract. This is the
form required when supplying it as a child of a certified structural layer. -/
def certifiedStructure (certified : ModuleCycleCertified ports) :
    ModuleCycleCertifiedStructure certified.cycleContract where
  moduleStructure := certified.moduleStructure
  certification := certified.certification

end ModuleCycleCertified

/-- Contracts required at the named child boundaries of one structural layer. -/
abbrev ChildCycleContracts (body : ModuleBody) :=
  (name : body.instancePorts.Name) →
    ModuleCycleContract (body.instancePorts.ports name)

namespace Certification.Layer

/-- Concrete child hierarchies certified against a layer's declared child
contracts. This is the implementation information supplied only when a
certified layer is instantiated. -/
abbrev ChildStructures (body : ModuleBody)
    (childContracts : ChildCycleContracts body) :=
  (name : body.instancePorts.Name) →
    ModuleCycleCertifiedStructure (childContracts name)

/-- The concrete composite hierarchy obtained by placing certified child
structures behind a structural layer. -/
abbrev moduleStructure (body : ModuleBody)
    {childContracts : ChildCycleContracts body}
    (children : ChildStructures body childContracts) :
    ModuleStructure body.ports :=
  .composite body fun name => (children name).moduleStructure

end Certification.Layer

/-- A cycle-certified, but still uninstantiated, structural layer. Its proof is
parametric in the concrete child hierarchies: any children certified against
the declared boundary contracts produce a parent hierarchy certified against
`cycleContract`. -/
structure ModuleCycleCertifiedLayer
    (body : ModuleBody)
    (childContracts : ChildCycleContracts body)
    (cycleContract : ModuleCycleContract body.ports) where
  certify : (children : Certification.Layer.ChildStructures body childContracts) →
    ModuleCycleCertification (Certification.Layer.moduleStructure body children)
      cycleContract

namespace ModuleCycleCertifiedLayer

/-- Instantiate a certified layer with certified child hierarchies. The
resulting structure is computed solely from the body and the children's
structure fields; proof fields contribute only the resulting certification. -/
noncomputable def instantiate
    (layer : ModuleCycleCertifiedLayer body childContracts cycleContract)
    (children : Certification.Layer.ChildStructures body childContracts) :
    ModuleCycleCertifiedStructure cycleContract where
  moduleStructure := Certification.Layer.moduleStructure body children
  certification := layer.certify children

/-- Certify an independently declared composite structure using a certified
layer and matching certified children. This keeps the routine dependent
transport out of individual module files. -/
noncomputable def certifyComposite
    (layer : ModuleCycleCertifiedLayer body childContracts cycleContract)
    (structuralChildren : (name : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports name))
    (children : Certification.Layer.ChildStructures body childContracts)
    (structureMatches : ∀ name,
      (children name).moduleStructure = structuralChildren name) :
    ModuleCycleCertification (.composite body structuralChildren) cycleContract := by
  have equal : (fun name => (children name).moduleStructure) =
      structuralChildren := by
    funext name
    exact structureMatches name
  cases equal
  exact layer.certify children

end ModuleCycleCertifiedLayer

namespace ModuleCycleCertifiedStructure

/-- Forget the fixed contract index and recover the general public bundle. -/
def bundle {ports : ModulePorts} {cycleContract : ModuleCycleContract ports}
    (certified : ModuleCycleCertifiedStructure cycleContract) :
    ModuleCycleCertified ports where
  moduleStructure := certified.moduleStructure
  cycleContract := cycleContract
  certification := certified.certification

end ModuleCycleCertifiedStructure

def ModuleCycleCertification.bundle {ports : ModulePorts}
    {moduleStructure : ModuleStructure ports}
    {cycleContract : ModuleCycleContract ports}
    (certification : ModuleCycleCertification moduleStructure cycleContract) :
    ModuleCycleCertified ports where
  moduleStructure := moduleStructure
  cycleContract := cycleContract
  certification := certification

/-! Transport a whole certification across a proved structure identity.  This
keeps dependent state/proposal casts at one generic boundary. -/
def ModuleCycleCertification.transportStructure {ports : ModulePorts}
    {source target : ModuleStructure ports}
    {cycleContract : ModuleCycleContract ports}
    (equal : source = target)
    (certification : ModuleCycleCertification source cycleContract) :
    ModuleCycleCertification target cycleContract := by
  cases equal
  exact certification

def ModuleCycleCertification.transportContract {ports : ModulePorts}
    {moduleStructure : ModuleStructure ports}
    {source target : ModuleCycleContract ports}
    (equal : source = target)
    (certification : ModuleCycleCertification moduleStructure source) :
    ModuleCycleCertification moduleStructure target := by
  cases equal
  exact certification

namespace ModuleCycleCertified

/-! Forwarding projections retain the convenient public interface while the
proof fields have a single owner in `ModuleCycleCertification`. -/

abbrev stateCorresponds (certified : ModuleCycleCertified ports) :=
  certified.certification.stateCorresponds

abbrev hasCorrespondingState (certified : ModuleCycleCertified ports) :=
  certified.certification.hasCorrespondingState

abbrev hasStructuralResult (certified : ModuleCycleCertified ports) :=
  certified.certification.hasStructuralResult

abbrev structuralResultUnique (certified : ModuleCycleCertified ports) :=
  certified.certification.structuralResultUnique

abbrev implements (certified : ModuleCycleCertified ports) :=
  certified.certification.implements

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

/-- Every structural solution agrees with the executable evaluation of the
public cycle contract. This is the generic bridge used by execution models: the
model can execute the contract without selecting a structural evaluator. -/
theorem solution_matches_evaluate
    (certified : ModuleCycleCertified ports)
    (inputs : ports.inputs.Values)
    (contractState : certified.cycleContract.state.Values)
    (structuralState : certified.moduleStructure.State)
    (proposal : ProposedValues certified.moduleStructure)
    (corresponds : certified.stateCorresponds contractState structuralState)
    (satisfies : certified.moduleStructure.IsSolution inputs structuralState proposal) :
    proposal.outputs = (certified.cycleContract.evaluate inputs contractState).1 ∧
      certified.stateCorresponds
        (certified.cycleContract.evaluate inputs contractState).2
        proposal.nextState := by
  rcases certified.implements inputs contractState structuralState proposal
      corresponds satisfies with
    ⟨nextContractState, evaluates, nextCorresponds⟩
  have unique := certified.cycleContract.evaluation_unique inputs contractState
    proposal.outputs (certified.cycleContract.evaluate inputs contractState).1
    nextContractState (certified.cycleContract.evaluate inputs contractState).2
    evaluates (certified.cycleContract.evaluate_evaluatesTo inputs contractState)
  rw [unique.2] at nextCorresponds
  exact ⟨unique.1, nextCorresponds⟩

/-! Certification turns each behavioral rule into a semantic dependency fact
about the independent structure. This is the generic child-rule interface used
by parent schedules; it does not inspect the certified module's implementation. -/

def structuralRule (certified : ModuleCycleCertified ports)
    (name : certified.cycleContract.RuleName) :
    StructuralRule certified.moduleStructure := by
  let rule := certified.cycleContract.outputRule name
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
  exact SignalGroup.Matches.eq_of_mem rule.writesOutputs
    leftHolds rightHolds output outputMem

end ModuleCycleCertified

end Silean.Contracts.Cycle
