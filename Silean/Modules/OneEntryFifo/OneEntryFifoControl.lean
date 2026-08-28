import Silean.Contracts.Cycle.CycleSchedule
import Silean.Naming.PrimitiveNaming
import Silean.Primitives

namespace Silean.Modules.OneEntryFifo.Control

open Silean

/-- Combinational handshake control for a fall-through one-entry FIFO. -/
inductive Input
  | storedValid
  | downstreamReady
deriving Enumeration

inductive Output
  | upstreamReady
  | storageUpdate
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun | .storedValid | .downstreamReady => .bit

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun | .upstreamReady | .storageUpdate => .bit

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

inductive Instance
  /-- Detects that the storage entry is empty. -/
  | invertValid
  /-- Makes the upstream ready when storage is empty or downstream is ready. -/
  | readyOr
  /-- Detects the two cases in which the storage-valid bit must change. -/
  | updateEq
deriving Enumeration

@[reducible] def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .invertValid => Primitives.not.ports
    | .readyOr => Primitives.or.ports
    | .updateEq => Primitives.eq.ports

@[reducible] def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    -- Expose the two control decisions directly.
    | .upstreamReady => context.instanceOutput .readyOr .output
    | .storageUpdate => context.instanceOutput .updateEq .output
  instanceInput
    -- Empty storage permits an upstream transfer without downstream readiness.
    | .invertValid, .input => context.moduleInput .storedValid
    | .readyOr, .left => context.moduleInput .downstreamReady
    | .readyOr, .right => context.instanceOutput .invertValid .output
    -- Storage changes when readiness and validity agree.
    | .updateEq, .left => context.moduleInput .downstreamReady
    | .updateEq, .right => context.moduleInput .storedValid

@[reducible] def body : ModuleBody := ⟨context, wiring⟩

@[reducible] def children : Contracts.Cycle.Certification.Children body
  | .invertValid => Primitives.notCertified
  | .readyOr => Primitives.orCertified
  | .updateEq => Primitives.eqCertified

@[reducible] def childStructure := Contracts.Cycle.Certification.childStructure children

def moduleStructure : ModuleStructure ports :=
  Contracts.Cycle.Certification.moduleStructure body children

/-! ## Exact cycle behavior and certification -/

inductive Rule
  | control
deriving Enumeration

def controlRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap
    (.ofLists [.bit, .bit] [.bit, .bit]) where
  readsInputs := (inputMap.select .downstreamReady).prepend .storedValid
  writesOutputs := (outputMap.select .storageUpdate).prepend .upstreamReady
  target
    | (storedValid, (downstreamReady, ())), _ =>
        (downstreamReady || !storedValid,
          ((downstreamReady && storedValid) ||
            (!downstreamReady && !storedValid), ()))

def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .control => ⟨_, controlRule⟩
  stateRule := Contracts.Cycle.CycleStateRule.empty ports
  outputCoverage := by rfl

abbrev invertRule : Contracts.Cycle.Certification.RuleOccurrence children :=
  ⟨.invertValid, Primitives.NotRule.apply⟩
abbrev readyRule : Contracts.Cycle.Certification.RuleOccurrence children :=
  ⟨.readyOr, Primitives.OrRule.apply⟩
abbrev updateRule : Contracts.Cycle.Certification.RuleOccurrence children :=
  ⟨.updateEq, Primitives.EqRule.apply⟩

@[simp] theorem invertRule_reads : invertRule.reads = [.input] := rfl
@[simp] theorem readyRule_reads : readyRule.reads = [.left, .right] := rfl
@[simp] theorem updateRule_reads : updateRule.reads = [.left, .right] := rfl
@[simp] theorem invertRule_writes : invertRule.writes = [.output] := rfl
@[simp] theorem readyRule_writes : readyRule.writes = [.output] := rfl
@[simp] theorem updateRule_writes : updateRule.writes = [.output] := rfl

def outputSchedule : Contracts.Cycle.Certification.OutputSchedule body children cycleContract .control :=
  .call invertRule
    (by intro port member; cases port; simp [cycleContract, controlRule,
      SignalSelection.prepend, SignalMap.select, SignalSelection.labels,
      Contracts.Cycle.Certification.sourceAvailable, body, wiring, context,
      EndpointContext.moduleInput])
    (by simp)
  (.call readyRule
    (by intro input member
        cases input with
        | left => simp [cycleContract, controlRule, SignalSelection.prepend,
            SignalMap.select, SignalSelection.labels, Contracts.Cycle.Certification.sourceAvailable,
            body, wiring, context, EndpointContext.moduleInput]
        | right => exact ⟨Primitives.NotRule.apply, by simp, by simp⟩)
    (by simp)
  (.call updateRule
    (by intro input member; cases input <;>
      simp [cycleContract, controlRule, SignalSelection.prepend,
        SignalMap.select, SignalSelection.labels, Contracts.Cycle.Certification.sourceAvailable,
        body, wiring, context, EndpointContext.moduleInput])
    (by simp)
  (.done (by
    intro output member
    cases output with
    | upstreamReady =>
        change Contracts.Cycle.Certification.outputAvailable
          ([updateRule, readyRule, invertRule] : Contracts.Cycle.Certification.Availability children)
          Instance.readyOr .output
        exact ⟨Primitives.OrRule.apply, by simp, by simp⟩
    | storageUpdate =>
        change Contracts.Cycle.Certification.outputAvailable
          ([updateRule, readyRule, invertRule] : Contracts.Cycle.Certification.Availability children)
          Instance.updateEq .output
        exact ⟨Primitives.EqRule.apply, by simp, by simp⟩))))

def stateSchedule : Contracts.Cycle.Certification.StateSchedule body children :=
  .done (by
    intro child input member
    cases child <;>
      simp [children, Primitives.notCertified, Primitives.notCycleContract,
        Primitives.orCertified, Primitives.orCycleContract,
        Primitives.eqCertified, Primitives.eqCycleContract,
        Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member)

def ruleSchedules : Contracts.Cycle.Certification.RuleSchedules body children cycleContract where
  output | .control => outputSchedule
  state := stateSchedule

theorem coversChildren : ruleSchedules.CoversChildren := by
  intro child rule
  cases child with
  | invertValid =>
    change Primitives.NotRule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
    apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs ruleSchedules .control
    change invertRule ∈ outputSchedule.finalAvailability
    simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | readyOr =>
    change Primitives.OrRule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
    apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs ruleSchedules .control
    change readyRule ∈ outputSchedule.finalAvailability
    simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | updateEq =>
    change Primitives.EqRule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
    apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs ruleSchedules .control
    change updateRule ∈ outputSchedule.finalAvailability
    simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

theorem hasAtMostOneSolution : moduleStructure.HasAtMostOneSolution :=
  ruleSchedules.hasAtMostOneSolution coversChildren

def invertInputs (inputs : ports.inputs.Values) : Primitives.not.ports.inputs.Values
  | .input => inputs .storedValid
def readyInputs (inputs : ports.inputs.Values)
    (invert : ProposedValues (children .invertValid).moduleStructure) :
    Primitives.or.ports.inputs.Values
  | .left => inputs .downstreamReady
  | .right => invert.outputs .output
def updateInputs (inputs : ports.inputs.Values) : Primitives.eq.ports.inputs.Values
  | .left => inputs .downstreamReady
  | .right => inputs .storedValid

theorem hasStructuralResult (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal := by
  rcases (children .invertValid).hasStructuralResult (invertInputs inputs)
      (currentState .invertValid) with ⟨invert, invertSatisfies⟩
  rcases (children .readyOr).hasStructuralResult (readyInputs inputs invert)
      (currentState .readyOr) with ⟨ready, readySatisfies⟩
  rcases (children .updateEq).hasStructuralResult (updateInputs inputs)
      (currentState .updateEq) with ⟨update, updateSatisfies⟩
  let childProposals : (name : Instance) → ProposedValues (childStructure name)
    | .invertValid => invert
    | .readyOr => ready
    | .updateEq => update
  let outputs : ports.outputs.Values := fun
    | .upstreamReady => ready.outputs .output
    | .storageUpdate => update.outputs .output
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output; cases output <;> rfl
  · intro child
    cases child with
    | invertValid =>
        change (children .invertValid).moduleStructure.IsSolution
          (ProposedValues.childInputs body childStructure inputs childProposals
            .invertValid) (currentState .invertValid) invert
        rw [show ProposedValues.childInputs body childStructure inputs
          childProposals .invertValid = invertInputs inputs by
            funext port; cases port; rfl]
        exact invertSatisfies
    | readyOr =>
        change (children .readyOr).moduleStructure.IsSolution
          (ProposedValues.childInputs body childStructure inputs childProposals
            .readyOr) (currentState .readyOr) ready
        rw [show ProposedValues.childInputs body childStructure inputs
          childProposals .readyOr = readyInputs inputs invert by
            funext port; cases port <;> rfl]
        exact readySatisfies
    | updateEq =>
        change (children .updateEq).moduleStructure.IsSolution
          (ProposedValues.childInputs body childStructure inputs childProposals
            .updateEq) (currentState .updateEq) update
        rw [show ProposedValues.childInputs body childStructure inputs
          childProposals .updateEq = updateInputs inputs by
            funext port; cases port <;> rfl]
        exact updateSatisfies

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : moduleStructure.State) : Prop := True

theorem controlRule_holds_iff (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values) :
    controlRule.Holds inputs state outputs ↔
      outputs .upstreamReady =
        (inputs .downstreamReady || !inputs .storedValid) ∧
      outputs .storageUpdate =
        ((inputs .downstreamReady && inputs .storedValid) ||
          (!inputs .downstreamReady && !inputs .storedValid)) := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, controlRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]

private theorem implements : Contracts.Cycle.Implements moduleStructure cycleContract stateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have invertImplements := Contracts.Cycle.Certification.childImplements children inputs structuralState
    proposal satisfies .invertValid SignalMap.emptyValues (by trivial)
  have readyImplements := Contracts.Cycle.Certification.childImplements children inputs structuralState
    proposal satisfies .readyOr SignalMap.emptyValues (by trivial)
  have updateImplements := Contracts.Cycle.Certification.childImplements children inputs structuralState
    proposal satisfies .updateEq SignalMap.emptyValues (by trivial)
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change controlRule.Holds inputs contractState proposal.outputs
    rw [controlRule_holds_iff]
    rcases proposal with ⟨outputs, children⟩
    rcases invertImplements with ⟨_, invertEvaluates, _⟩
    rcases readyImplements with ⟨_, readyEvaluates, _⟩
    rcases updateImplements with ⟨_, updateEvaluates, _⟩
    have invertOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (invertEvaluates.1 Primitives.NotRule.apply)
    have readyOutput := (Primitives.orOutputRule_holds_iff _ _ _).mp
      (readyEvaluates.1 Primitives.OrRule.apply)
    have updateOutput := (Primitives.eqOutputRule_holds_iff _ _ _).mp
      (updateEvaluates.1 Primitives.EqRule.apply)
    have readyBoundary := boundary Output.upstreamReady
    have updateBoundary := boundary Output.storageUpdate
    change outputs .upstreamReady =
        (inputs .downstreamReady || !inputs .storedValid) ∧
      outputs .storageUpdate =
        ((inputs .downstreamReady && inputs .storedValid) ||
          (!inputs .downstreamReady && !inputs .storedValid))
    have readyEq : outputs .upstreamReady =
        (children .readyOr).outputs .output := by
      simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using readyBoundary
    have updateEq : outputs .storageUpdate =
        (children .updateEq).outputs .output := by
      simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using updateBoundary
    have invertEq : (children .invertValid).outputs .output =
        !inputs .storedValid := by
      simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, SignalSource.value] using
        invertOutput
    have readyChild : (children .readyOr).outputs .output =
        (inputs .downstreamReady || (children .invertValid).outputs .output) := by
      simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using readyOutput
    have updateChild : (children .updateEq).outputs .output =
        ((inputs .downstreamReady && inputs .storedValid) ||
          (!inputs .downstreamReady && !inputs .storedValid)) := by
      simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, SignalSource.value] using
        updateOutput
    constructor
    · exact readyEq.trans (readyChild.trans
        (congrArg (fun value => inputs .downstreamReady || value) invertEq))
    · exact updateEq.trans updateChild
  · rfl

noncomputable opaque certification :
    Contracts.Cycle.ModuleCycleCertification moduleStructure cycleContract := {
  stateCorresponds := stateCorresponds,
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
  hasStructuralResult := hasStructuralResult,
  structuralResultUnique := hasAtMostOneSolution,
  implements := implements }

noncomputable def certified : Contracts.Cycle.ModuleCycleCertified ports :=
  certification.bundle

@[simp] theorem certified_cycleContract :
    certified.cycleContract = cycleContract := rfl

theorem hasExactlyOneSolution (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal ∧
      ∀ other, moduleStructure.IsSolution inputs currentState other →
        other = proposal :=
  certified.hasExactlyOneStructuralResult inputs currentState

end Silean.Modules.OneEntryFifo.Control

namespace Silean.Modules.OneEntryFifo.Control.Naming

open Silean Silean.Naming

def ports : ModulePortsNaming Modules.OneEntryFifo.Control.ports where
  inputs := ⟨fun
    | .storedValid => "stored_valid"
    | .downstreamReady => "downstream_ready"⟩
  outputs := ⟨fun
    | .upstreamReady => "upstream_ready"
    | .storageUpdate => "storage_update"⟩

def naming : ModuleNaming Modules.OneEntryFifo.Control.moduleStructure := by
  unfold Modules.OneEntryFifo.Control.moduleStructure Contracts.Cycle.Certification.moduleStructure
  exact .composite ⟨"one_entry_fifo_control", "structural", []⟩ ports
    (fun
      | .invertValid => "invert_valid"
      | .readyOr => "ready_or"
      | .updateEq => "update_eq")
    (fun
      | .invertValid => Silean.Naming.Primitive.not
      | .readyOr => Silean.Naming.Primitive.or
      | .updateEq => Silean.Naming.Primitive.eq)

end Silean.Modules.OneEntryFifo.Control.Naming
