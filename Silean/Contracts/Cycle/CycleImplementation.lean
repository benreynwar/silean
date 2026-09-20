import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Semantics.StructuralDependency

namespace Silean.Contracts.Cycle

/-! # Certifying a structure against a cycle contract

Cycle certification relates the contract's deliberately behavioral state to
the module's recursively derived structural state. The correspondence need not
be equality or a computable function, but it must cover every structural state
and be preserved by every cycle.

Implementation quantifies over every complete solution of the structural
equations, so neither a proof schedule nor a chosen evaluator defines what it
means to satisfy the contract. Existence and uniqueness of those solutions are
separate required proofs. -/

/-- Hierarchy-witness proof form used internally when constructing a
certification. The public relation below hides this witness behind its root
boundary step. -/
def ImplementsSolutions {ports : ModulePorts}
    (moduleStructure : ModuleStructure ports)
    (cycleContract : ModuleCycleContract ports)
    (stateCorresponds : cycleContract.state.Values →
      moduleStructure.State → Prop) : Prop :=
  ∀ contractState (hierStep : HierStep moduleStructure),
    stateCorresponds contractState
      (HierStep.currentState moduleStructure hierStep) →
    moduleStructure.IsSolution hierStep →
      ∃ nextContractState,
        cycleContract.Allows
          { inputs := hierStep.inputs
            currentState := contractState
            outputs := hierStep.outputs
            nextState := nextContractState } ∧
        stateCorresponds nextContractState
          (HierStep.nextState moduleStructure hierStep)

/-- A structure implements a contract when every realizable structural
boundary step induces an allowed contract step with the same inputs and
outputs, while preserving the relation between behavioral and structural
state. Internal equation assignments are hidden by `ModuleStructure.Realizes`.
-/
def Implements {ports : ModulePorts}
    (moduleStructure : ModuleStructure ports)
    (cycleContract : ModuleCycleContract ports)
    (stateCorresponds : cycleContract.state.Values →
      moduleStructure.State → Prop) : Prop :=
  ∀ contractState (structuralStep : moduleStructure.Step),
    stateCorresponds contractState structuralStep.currentState →
    moduleStructure.Realizes structuralStep →
      ∃ nextContractState,
        cycleContract.Allows
          { inputs := structuralStep.inputs
            currentState := contractState
            outputs := structuralStep.outputs
            nextState := nextContractState } ∧
        stateCorresponds nextContractState structuralStep.nextState

/-- The hierarchy-witness proof form and the public boundary-step relation
express exactly the same implementation claim. -/
theorem implementsSolutions_iff_implements {ports : ModulePorts}
    {moduleStructure : ModuleStructure ports}
    {cycleContract : ModuleCycleContract ports}
    {stateCorresponds : cycleContract.state.Values →
      moduleStructure.State → Prop} :
    ImplementsSolutions moduleStructure cycleContract stateCorresponds ↔
      Implements moduleStructure cycleContract stateCorresponds := by
  constructor
  · intro implements contractState structuralStep corresponds realizes
    rcases realizes with ⟨hierStep, solution, rootEqual⟩
    subst structuralStep
    exact implements contractState hierStep corresponds solution
  · intro implements contractState hierStep corresponds solution
    exact implements contractState hierStep.step corresponds
      (ModuleStructure.realizes_of_solution solution)

/-! Correctness evidence for an already chosen structure and contract.  Keeping
these as parameters is important: executable consumers can use the structure
without evaluating this (generally noncomputable) proof object. -/

structure ModuleCycleCertification {ports : ModulePorts}
    (moduleStructure : ModuleStructure ports)
    (cycleContract : ModuleCycleContract ports) where
  /-- Contract-independent existence and uniqueness of structural solutions. -/
  structural : ModuleStructuralCertification moduleStructure
  /-- Relation between behavioral state and the hierarchy's physical state. -/
  stateCorresponds : cycleContract.state.Values → moduleStructure.State → Prop
  /-- Every physical state has at least one behavioral description. -/
  hasCorrespondingState : ∀ structuralState,
    ∃ contractState, stateCorresponds contractState structuralState
  /-- Every structural solution follows the contract and preserves correspondence. -/
  implements : Implements moduleStructure cycleContract stateCorresponds

namespace ModuleCycleCertification

/-- Use a certification without exposing its internal equation assignment:
every realizable structural step induces an allowed contract step with the
same boundary inputs and outputs. -/
theorem allows_of_realizes
    {moduleStructure : ModuleStructure ports}
    {cycleContract : ModuleCycleContract ports}
    (certification : ModuleCycleCertification moduleStructure cycleContract)
    (contractState : cycleContract.state.Values)
    (structuralStep : moduleStructure.Step)
    (corresponds : certification.stateCorresponds contractState
      structuralStep.currentState)
    (realizes : moduleStructure.Realizes structuralStep) :
    ∃ nextContractState,
      cycleContract.Allows
        { inputs := structuralStep.inputs
          currentState := contractState
          outputs := structuralStep.outputs
          nextState := nextContractState } ∧
      certification.stateCorresponds nextContractState
        structuralStep.nextState :=
  certification.implements contractState structuralStep corresponds realizes

end ModuleCycleCertification

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

/-! Transport a whole certification across a proved structure identity. This
keeps dependent structural-state and witness casts at one generic boundary. -/
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

/-- Forget behavioral targets and contract state, retaining only the boundary
dependency declarations needed by structural composition. -/
@[reducible] def ModuleCycleContract.structuralRules
    (contract : ModuleCycleContract ports) : ModuleStructuralRules ports where
  RuleName := contract.RuleName
  ruleNames := contract.ruleNames
  rule := fun name => {
    reads := (contract.outputRule name).readsInputs.labels
    writes := (contract.outputRule name).writesOutputs.labels }
  outputCoverage := contract.outputCoverage

namespace ModuleCycleCertified

/-! Forwarding projections retain the convenient public interface while the
proof fields have a single owner in `ModuleCycleCertification`. -/

abbrev stateCorresponds (certified : ModuleCycleCertified ports) :=
  certified.certification.stateCorresponds

abbrev hasCorrespondingState (certified : ModuleCycleCertified ports) :=
  certified.certification.hasCorrespondingState

/-- Contract-independent structural evidence carried by a cycle-certified
module. -/
abbrev structuralCertification (certified : ModuleCycleCertified ports) :=
  certified.certification.structural

abbrev implements (certified : ModuleCycleCertified ports) :=
  certified.certification.implements

/-! A certificate already contains exactly the two order-independent facts
needed for existence and uniqueness. No selected evaluator is required. -/

theorem hasExactlyOneStructuralResult
    (certified : ModuleCycleCertified ports)
    (inputs : ports.inputs.Values)
    (structuralState : certified.moduleStructure.State) :
    ∃ hierStep,
      certified.moduleStructure.IsSolution hierStep ∧
      hierStep.inputs = inputs ∧
      HierStep.currentState certified.moduleStructure hierStep =
        structuralState ∧
      ∀ other,
        certified.moduleStructure.IsSolution other →
        other.inputs = inputs →
        HierStep.currentState certified.moduleStructure other =
          structuralState →
        other = hierStep := by
  rcases certified.certification.structural.hasSolution inputs structuralState with
    ⟨hierStep, satisfies, inputsEqual, stateEqual⟩
  refine ⟨hierStep, satisfies, inputsEqual, stateEqual, ?_⟩
  intro other otherSatisfies otherInputsEqual otherStateEqual
  exact certified.certification.structural.hasAtMostOneSolution other hierStep
    otherSatisfies satisfies
    (otherInputsEqual.trans inputsEqual.symm)
    (otherStateEqual.trans stateEqual.symm)

/-- Every realizable structural boundary step agrees with executable contract
evaluation. Execution models use this theorem without opening the hierarchy
witness hidden by `Realizes`. -/
theorem realization_matches_evaluate
    (certified : ModuleCycleCertified ports)
    (contractState : certified.cycleContract.state.Values)
    {structuralStep : certified.moduleStructure.Step}
    (corresponds : certified.stateCorresponds contractState
      structuralStep.currentState)
    (realizes : certified.moduleStructure.Realizes structuralStep) :
    structuralStep.outputs =
        (certified.cycleContract.evaluate structuralStep.inputs contractState).1 ∧
      certified.stateCorresponds
        (certified.cycleContract.evaluate structuralStep.inputs contractState).2
        structuralStep.nextState := by
  rcases certified.implements contractState structuralStep corresponds realizes with
    ⟨nextContractState, allowed, nextCorresponds⟩
  rcases certified.cycleContract.allowed_result_eq_evaluate allowed with
    ⟨outputsEqual, nextStateEqual⟩
  change structuralStep.outputs =
    (certified.cycleContract.evaluate structuralStep.inputs contractState).1
    at outputsEqual
  change nextContractState =
    (certified.cycleContract.evaluate structuralStep.inputs contractState).2
    at nextStateEqual
  rw [nextStateEqual] at nextCorresponds
  exact ⟨outputsEqual, nextCorresponds⟩

/-- The hierarchy-witness form of `realization_matches_evaluate`, useful while
constructing structural proofs. Boundary-level consumers should use the
realization theorem above. -/
theorem solution_matches_evaluate
    (certified : ModuleCycleCertified ports)
    (contractState : certified.cycleContract.state.Values)
    (hierStep : HierStep certified.moduleStructure)
    (corresponds : certified.stateCorresponds contractState
      (HierStep.currentState certified.moduleStructure hierStep))
    (satisfies : certified.moduleStructure.IsSolution hierStep) :
    hierStep.outputs =
        (certified.cycleContract.evaluate hierStep.inputs contractState).1 ∧
      certified.stateCorresponds
        (certified.cycleContract.evaluate hierStep.inputs contractState).2
        (HierStep.nextState certified.moduleStructure hierStep) :=
  certified.realization_matches_evaluate contractState corresponds
    (ModuleStructure.realizes_of_solution satisfies)

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
  intro left right leftSatisfies rightSatisfies statesEqual
    inputsAgree output outputMem
  rcases certified.hasCorrespondingState
      (HierStep.currentState certified.moduleStructure left) with
    ⟨contractState, corresponds⟩
  rcases certified.implements contractState left.step
      corresponds (ModuleStructure.realizes_of_solution leftSatisfies) with
    ⟨leftNext, leftAllowed, leftNextCorresponds⟩
  have rightCorresponds : certified.stateCorresponds contractState
      (HierStep.currentState certified.moduleStructure right) := by
    rw [← statesEqual]
    exact corresponds
  rcases certified.implements contractState
      right.step rightCorresponds
      (ModuleStructure.realizes_of_solution rightSatisfies) with
    ⟨rightNext, rightAllowed, rightNextCorresponds⟩
  have selectedInputsEqual :
      rule.readsInputs.project left.inputs =
        rule.readsInputs.project right.inputs :=
    rule.readsInputs.project_eq_of_eq_on left.inputs right.inputs inputsAgree
  have leftHolds := leftAllowed.1 name
  have rightHolds := rightAllowed.1 name
  unfold CycleOutputRule.Holds at leftHolds rightHolds
  change rule.writesOutputs.Matches left.outputs
    (rule.target (rule.readsInputs.project left.inputs) contractState) at leftHolds
  change rule.writesOutputs.Matches right.outputs
    (rule.target (rule.readsInputs.project right.inputs) contractState) at rightHolds
  rw [selectedInputsEqual] at leftHolds
  exact SignalGroup.Matches.eq_of_mem rule.writesOutputs
    leftHolds rightHolds output outputMem

/-- A cycle certification automatically certifies the dependency-only rule
interface obtained by forgetting the cycle rules' behavioral targets. -/
theorem structuralRuleCertification (certified : ModuleCycleCertified ports) :
    ModuleStructuralRuleCertification certified.moduleStructure
      certified.cycleContract.structuralRules where
  structural := certified.certification.structural
  determines := fun name => (certified.structuralRule name).determines

/-- View a cycle-certified module as a contract-independent structurally
certified child while retaining its fine-grained output dependencies. -/
def structuralCertifiedStructure (certified : ModuleCycleCertified ports) :
    ModuleStructuralCertifiedStructure certified.cycleContract.structuralRules where
  moduleStructure := certified.moduleStructure
  certification := certified.structuralRuleCertification

end ModuleCycleCertified

namespace ModuleCycleCertifiedStructure

/-- Contract-independent structural view of a structure certified against a
fixed cycle contract. -/
def structuralCertifiedStructure
    {cycleContract : ModuleCycleContract ports}
    (certified : ModuleCycleCertifiedStructure cycleContract) :
    ModuleStructuralCertifiedStructure cycleContract.structuralRules :=
  certified.bundle.structuralCertifiedStructure

end ModuleCycleCertifiedStructure

end Silean.Contracts.Cycle
