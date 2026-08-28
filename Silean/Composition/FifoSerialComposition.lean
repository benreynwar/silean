import Silean.Contracts.Fifo.FifoCycleBehavior
import Silean.Contracts.Cycle.CycleSchedule
import Silean.Naming.FifoPortsNaming

namespace Silean.Composition.FifoSerial

open Silean
open Contracts.Fifo.Cycle

/-! Connects two FIFO implementations in series. The upstream FIFO accepts the
external input, the downstream FIFO drives the external output, and their
valid/ready boundaries are connected internally. -/

private inductive Instance
  /-- The FIFO nearest the external input. -/
  | upstream
  /-- The FIFO nearest the external output. -/
  | downstream
deriving Enumeration

@[reducible] private def instancePorts (signalType : SignalType) : InstancePorts :=
  EnumeratedMap.of Instance fun _ => Silean.Interfaces.Fifo.ports signalType

@[reducible] private def context (signalType : SignalType) : EndpointContext where
  ports := Silean.Interfaces.Fifo.ports signalType
  instancePorts := instancePorts signalType

private def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instancePorts :=
  let c := context signalType
  { moduleOutput := fun
    -- Outputs come from the corresponding end of the chain.
    | .outputValid => c.instanceOutput .downstream .outputValid
    | .outputData => c.instanceOutput .downstream .outputData
    | .inputReady => c.instanceOutput .upstream .inputReady
    instanceInput := fun
    -- External input enters the upstream FIFO; downstream readiness flows back.
    | .upstream, .inputValid => c.moduleInput .inputValid
    | .upstream, .inputData => c.moduleInput .inputData
    | .upstream, .outputReady =>
        c.instanceOutput .downstream .inputReady
    | .upstream, .reset => c.moduleInput .reset
    -- Upstream output enters the downstream FIFO; external readiness terminates it.
    | .downstream, .inputValid =>
        c.instanceOutput .upstream .outputValid
    | .downstream, .inputData =>
        c.instanceOutput .upstream .outputData
    | .downstream, .outputReady => c.moduleInput .outputReady
    | .downstream, .reset => c.moduleInput .reset }

@[reducible] private def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

def moduleStructure (signalType : SignalType)
    (upstream downstream : ModuleStructure (Silean.Interfaces.Fifo.ports signalType)) :
    ModuleStructure (Silean.Interfaces.Fifo.ports signalType) :=
  .composite (body signalType) fun
    | .upstream => upstream
    | .downstream => downstream

/-! ## Cycle certification -/

@[reducible] private noncomputable def children
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Certification.Children (body signalType)
  | .upstream => upstream.certified
  | .downstream => downstream.certified

private abbrev upstreamForward (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Certification.RuleOccurrence (children upstream downstream) :=
  ⟨.upstream, Contracts.Fifo.Cycle.Rule.forward⟩

private abbrev upstreamReady (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Certification.RuleOccurrence (children upstream downstream) :=
  ⟨.upstream, Contracts.Fifo.Cycle.Rule.ready⟩

private abbrev downstreamForward (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Certification.RuleOccurrence (children upstream downstream) :=
  ⟨.downstream, Contracts.Fifo.Cycle.Rule.forward⟩

private abbrev downstreamReady (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Certification.RuleOccurrence (children upstream downstream) :=
  ⟨.downstream, Contracts.Fifo.Cycle.Rule.ready⟩

@[simp] private theorem upstreamForward_reads
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    (upstreamForward upstream downstream).reads = [.inputValid, .inputData] := rfl
@[simp] private theorem upstreamForward_writes
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    (upstreamForward upstream downstream).writes = [.outputValid, .outputData] := rfl
@[simp] private theorem upstreamReady_reads
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    (upstreamReady upstream downstream).reads = [.outputReady] := rfl
@[simp] private theorem upstreamReady_writes
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    (upstreamReady upstream downstream).writes = [.inputReady] := rfl
@[simp] private theorem downstreamForward_reads
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    (downstreamForward upstream downstream).reads = [.inputValid, .inputData] := rfl
@[simp] private theorem downstreamForward_writes
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    (downstreamForward upstream downstream).writes = [.outputValid, .outputData] := rfl
@[simp] private theorem downstreamReady_reads
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    (downstreamReady upstream downstream).reads = [.outputReady] := rfl
@[simp] private theorem downstreamReady_writes
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    (downstreamReady upstream downstream).writes = [.inputReady] := rfl

private def forwardSchedule (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Certification.OutputSchedule (body signalType) (children upstream downstream)
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract .forward :=
  .call (upstreamForward upstream downstream)
    (by
      intro input member
      cases input with
      | inputValid | inputData =>
          simp [Contracts.Cycle.Certification.sourceAvailable, body, wiring, context,
            EndpointContext.moduleInput]
      | outputReady | reset => simp at member)
    (by simp)
  (.call (downstreamForward upstream downstream)
    (by
      intro input member
      cases input with
      | inputValid | inputData =>
          exact ⟨Contracts.Fifo.Cycle.Rule.forward, by simp, by simp⟩
      | outputReady | reset => simp at member)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | outputValid | outputData =>
        exact ⟨Contracts.Fifo.Cycle.Rule.forward, by simp, by simp⟩
    | inputReady => simp at member)))

private def readySchedule (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Certification.OutputSchedule (body signalType) (children upstream downstream)
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract .ready :=
  .call (downstreamReady upstream downstream)
    (by
      intro input member
      cases input with
      | outputReady =>
          simp [Contracts.Cycle.Certification.sourceAvailable, body, wiring, context,
            EndpointContext.moduleInput]
      | inputValid | inputData | reset => simp at member)
    (by simp)
  (.call (upstreamReady upstream downstream)
    (by
      intro input member
      cases input with
      | outputReady => exact ⟨Contracts.Fifo.Cycle.Rule.ready, by simp, by simp⟩
      | inputValid | inputData | reset => simp at member)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | inputReady => exact ⟨Contracts.Fifo.Cycle.Rule.ready, by simp, by simp⟩
    | outputValid | outputData => simp at member)))

private def stateSchedule (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Certification.StateSchedule (body signalType) (children upstream downstream) :=
  .call (upstreamForward upstream downstream)
    (by
      intro input member
      cases input with
      | inputValid | inputData =>
          simp [Contracts.Cycle.Certification.sourceAvailable, body, wiring, context,
            EndpointContext.moduleInput]
      | outputReady | reset => simp at member) (by simp)
  (.call (downstreamForward upstream downstream)
    (by
      intro input member
      cases input with
      | inputValid | inputData =>
          exact ⟨Contracts.Fifo.Cycle.Rule.forward, by simp, by simp⟩
      | outputReady | reset => simp at member)
    (by simp)
  (.call (downstreamReady upstream downstream)
    (by
      intro input member
      cases input with
      | outputReady =>
          simp [Contracts.Cycle.Certification.sourceAvailable, body, wiring, context,
            EndpointContext.moduleInput]
      | inputValid | inputData | reset => simp at member) (by simp)
  (.call (upstreamReady upstream downstream)
    (by
      intro input member
      cases input with
      | outputReady => exact ⟨Contracts.Fifo.Cycle.Rule.ready, by simp, by simp⟩
      | inputValid | inputData | reset => simp at member)
    (by simp)
  (.done (by
    intro child input member
    cases child with
    | upstream =>
        cases input with
        | inputValid | inputData | reset => trivial
        | outputReady => exact ⟨Contracts.Fifo.Cycle.Rule.ready, by simp, by simp⟩
    | downstream =>
        cases input with
        | inputValid | inputData =>
            exact ⟨Contracts.Fifo.Cycle.Rule.forward, by simp, by simp⟩
        | outputReady | reset => trivial)))))

private def ruleSchedules (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Certification.RuleSchedules (body signalType) (children upstream downstream)
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract where
  output
    | .forward => forwardSchedule upstream downstream
    | .ready => readySchedule upstream downstream
  state := stateSchedule upstream downstream

private theorem coversChildren (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    (ruleSchedules upstream downstream).CoversChildren := by
  intro child rule
  cases child with
  | upstream =>
      change Contracts.Fifo.Cycle.Rule at rule
      cases rule with
      | forward =>
          apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
          change upstreamForward upstream downstream ∈
            (stateSchedule upstream downstream).finalAvailability
          simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
      | ready =>
          apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
          change upstreamReady upstream downstream ∈
            (stateSchedule upstream downstream).finalAvailability
          simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | downstream =>
      change Contracts.Fifo.Cycle.Rule at rule
      cases rule with
      | forward =>
          apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
          change downstreamForward upstream downstream ∈
            (stateSchedule upstream downstream).finalAvailability
          simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
      | ready =>
          apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
          change downstreamReady upstream downstream ∈
            (stateSchedule upstream downstream).finalAvailability
          simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

private theorem hasAtMostOneSolution
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children upstream downstream)).HasAtMostOneSolution :=
  (ruleSchedules upstream downstream).hasAtMostOneSolution
    (coversChildren upstream downstream)

private theorem moduleStructure_eq
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    moduleStructure signalType upstream.moduleStructure downstream.moduleStructure =
      Contracts.Cycle.Certification.moduleStructure (body signalType) (children upstream downstream) := by
  unfold moduleStructure Contracts.Cycle.Certification.moduleStructure
  congr
  funext child
  cases child <;> rfl

private def upstreamInputs (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (_upstreamState : upstream.state.Values)
    (downstreamState : downstream.state.Values) :
    (Silean.Interfaces.Fifo.ports signalType).inputs.Values
  | .inputValid => inputs .inputValid
  | .inputData => inputs .inputData
  | .outputReady => downstream.ready (inputs .outputReady) downstreamState
  | .reset => inputs .reset

private def downstreamInputs (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (upstreamState : upstream.state.Values)
    (_downstreamState : downstream.state.Values) :
    (Silean.Interfaces.Fifo.ports signalType).inputs.Values
  | .inputValid => (upstream.forward (inputs .inputValid) (inputs .inputData)
      upstreamState).1
  | .inputData => (upstream.forward (inputs .inputValid) (inputs .inputData)
      upstreamState).2
  | .outputReady => inputs .outputReady
  | .reset => inputs .reset

private def stateCorresponds (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType)
    (contractState : (upstream.cycleBehavior.serial downstream.cycleBehavior).state.Values)
    (structuralState : (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children upstream downstream)).State) : Prop :=
  upstream.certified.stateCorresponds (Contracts.Fifo.Cycle.leftState contractState)
      (structuralState .upstream) ∧
    downstream.certified.stateCorresponds (Contracts.Fifo.Cycle.rightState contractState)
      (structuralState .downstream)

private theorem hasCorrespondingState
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType)
    (structuralState : (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children upstream downstream)).State) :
    ∃ contractState, stateCorresponds upstream downstream contractState structuralState := by
  rcases upstream.certified.hasCorrespondingState (structuralState .upstream) with
    ⟨upstreamState, upstreamCorresponds⟩
  rcases downstream.certified.hasCorrespondingState (structuralState .downstream) with
    ⟨downstreamState, downstreamCorresponds⟩
  exact ⟨Contracts.Fifo.Cycle.combineState upstreamState downstreamState,
    ⟨upstreamCorresponds, downstreamCorresponds⟩⟩

private theorem hasStructuralResult
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType)
    (inputs : (Silean.Interfaces.Fifo.ports signalType).inputs.Values)
    (structuralState : (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children upstream downstream)).State) :
    ∃ proposal, (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children upstream downstream)).IsSolution inputs structuralState proposal := by
  rcases upstream.certified.hasCorrespondingState (structuralState .upstream) with
    ⟨upstreamState, upstreamCorresponds⟩
  rcases downstream.certified.hasCorrespondingState (structuralState .downstream) with
    ⟨downstreamState, downstreamCorresponds⟩
  let upstreamInput := upstreamInputs upstream.cycleBehavior downstream.cycleBehavior
    inputs upstreamState downstreamState
  let downstreamInput := downstreamInputs upstream.cycleBehavior downstream.cycleBehavior
    inputs upstreamState downstreamState
  rcases upstream.certified.hasStructuralResult upstreamInput
      (structuralState .upstream) with ⟨upstreamProposal, upstreamSatisfies⟩
  rcases downstream.certified.hasStructuralResult downstreamInput
      (structuralState .downstream) with ⟨downstreamProposal, downstreamSatisfies⟩
  have upstreamMatches := upstream.certified.solution_matches_evaluate upstreamInput
    upstreamState (structuralState .upstream) upstreamProposal upstreamCorresponds
    upstreamSatisfies
  have downstreamMatches := downstream.certified.solution_matches_evaluate downstreamInput
    downstreamState (structuralState .downstream) downstreamProposal
    downstreamCorresponds downstreamSatisfies
  have upstreamForward := upstream.cycleBehavior.evaluate_forward upstreamInput upstreamState
  have upstreamReady := upstream.cycleBehavior.evaluate_ready upstreamInput upstreamState
  have downstreamForward := downstream.cycleBehavior.evaluate_forward downstreamInput downstreamState
  have downstreamReady := downstream.cycleBehavior.evaluate_ready downstreamInput downstreamState
  dsimp only at upstreamForward upstreamReady downstreamForward downstreamReady
  have upstreamMatch : upstreamProposal.outputs =
      (upstream.cycleBehavior.cycleContract.evaluate upstreamInput upstreamState).1 :=
    upstreamMatches.1
  have downstreamMatch : downstreamProposal.outputs =
      (downstream.cycleBehavior.cycleContract.evaluate downstreamInput downstreamState).1 :=
    downstreamMatches.1
  rw [← upstreamMatch] at upstreamForward upstreamReady
  rw [← downstreamMatch] at downstreamForward downstreamReady
  let childProposals : (name : Instance) → ProposedValues
      (Contracts.Cycle.Certification.childStructure (children upstream downstream) name)
    | .upstream => upstreamProposal
    | .downstream => downstreamProposal
  let outputs : (Silean.Interfaces.Fifo.ports signalType).outputs.Values := fun
    | .outputValid => downstreamProposal.outputs .outputValid
    | .outputData => downstreamProposal.outputs .outputData
    | .inputReady => upstreamProposal.outputs .inputReady
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output
    cases output <;> rfl
  · intro child
    cases child with
    | upstream =>
        change upstream.moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType)
            (Contracts.Cycle.Certification.childStructure (children upstream downstream)) inputs
            childProposals .upstream) (structuralState .upstream) upstreamProposal
        rw [show ProposedValues.childInputs (body signalType)
            (Contracts.Cycle.Certification.childStructure (children upstream downstream)) inputs
            childProposals .upstream = upstreamInput by
          funext port
          cases port with
          | inputValid | inputData | reset => rfl
          | outputReady =>
              change downstreamProposal.outputs .inputReady = _
              exact downstreamReady]
        exact upstreamSatisfies
    | downstream =>
        change downstream.moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType)
            (Contracts.Cycle.Certification.childStructure (children upstream downstream)) inputs
            childProposals .downstream) (structuralState .downstream)
              downstreamProposal
        rw [show ProposedValues.childInputs (body signalType)
            (Contracts.Cycle.Certification.childStructure (children upstream downstream)) inputs
            childProposals .downstream = downstreamInput by
          funext port
          cases port with
          | inputValid => exact upstreamForward.1
          | inputData => exact upstreamForward.2
          | outputReady | reset => rfl]
        exact downstreamSatisfies

private theorem implements
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Implements (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children upstream downstream))
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract
      (stateCorresponds upstream downstream) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have upstreamMatches := Contracts.Cycle.Certification.childSolutionMatchesContract
    (children upstream downstream)
    inputs structuralState proposal satisfies .upstream
      (Contracts.Fifo.Cycle.leftState contractState) corresponds.1
  have downstreamMatches := Contracts.Cycle.Certification.childSolutionMatchesContract
    (children upstream downstream)
    inputs structuralState proposal satisfies .downstream
      (Contracts.Fifo.Cycle.rightState contractState) corresponds.2
  rcases proposal with ⟨outputs, childProposals⟩
  rcases upstreamMatches with ⟨upstreamEvaluates, upstreamNextCorresponds⟩
  rcases downstreamMatches with ⟨downstreamEvaluates, downstreamNextCorresponds⟩
  let upstreamActual := ProposedValues.childInputs (body signalType)
    (Contracts.Cycle.Certification.childStructure (children upstream downstream)) inputs
      childProposals .upstream
  let downstreamActual := ProposedValues.childInputs (body signalType)
    (Contracts.Cycle.Certification.childStructure (children upstream downstream)) inputs
      childProposals .downstream
  have upstreamForward := (upstream.cycleBehavior.forwardRule_holds_iff upstreamActual
    (Contracts.Fifo.Cycle.leftState contractState) (childProposals .upstream).outputs).mp
      (upstreamEvaluates.1 .forward)
  have upstreamReady := (upstream.cycleBehavior.readyRule_holds_iff upstreamActual
    (Contracts.Fifo.Cycle.leftState contractState) (childProposals .upstream).outputs).mp
      (upstreamEvaluates.1 .ready)
  have downstreamForward := (downstream.cycleBehavior.forwardRule_holds_iff downstreamActual
    (Contracts.Fifo.Cycle.rightState contractState) (childProposals .downstream).outputs).mp
      (downstreamEvaluates.1 .forward)
  have downstreamReady := (downstream.cycleBehavior.readyRule_holds_iff downstreamActual
    (Contracts.Fifo.Cycle.rightState contractState) (childProposals .downstream).outputs).mp
      (downstreamEvaluates.1 .ready)
  change (childProposals .upstream).outputs .outputValid =
      (upstream.cycleBehavior.forward (inputs .inputValid) (inputs .inputData)
        (Contracts.Fifo.Cycle.leftState contractState)).1 ∧
    (childProposals .upstream).outputs .outputData =
      (upstream.cycleBehavior.forward (inputs .inputValid) (inputs .inputData)
        (Contracts.Fifo.Cycle.leftState contractState)).2 at upstreamForward
  change (childProposals .downstream).outputs .inputReady =
    downstream.cycleBehavior.ready (inputs .outputReady)
      (Contracts.Fifo.Cycle.rightState contractState) at downstreamReady
  have upstreamActual_eq : upstreamActual =
      upstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
        (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState) := by
    funext port
    cases port with
    | inputValid | inputData | reset => rfl
    | outputReady =>
        change (childProposals .downstream).outputs .inputReady = _
        exact downstreamReady
  have downstreamActual_eq : downstreamActual =
      downstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
        (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState) := by
    funext port
    cases port with
    | inputValid =>
        change (childProposals .upstream).outputs .outputValid = _
        exact upstreamForward.1
    | inputData =>
        change (childProposals .upstream).outputs .outputData = _
        exact upstreamForward.2
    | outputReady | reset => rfl
  rw [upstreamActual_eq] at upstreamReady
  rw [downstreamActual_eq] at downstreamForward
  let nextContractState :=
    (upstream.cycleBehavior.serial downstream.cycleBehavior).nextState inputs contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule with
      | forward =>
          change (upstream.cycleBehavior.serial downstream.cycleBehavior).forwardRule.Holds
            inputs contractState outputs
          rw [Contracts.Fifo.Cycle.CycleBehavior.forwardRule_holds_iff]
          have boundary := satisfies.1
          constructor
          · exact (boundary .outputValid).trans (by
              change (childProposals .downstream).outputs .outputValid = _
              simpa [Contracts.Fifo.Cycle.CycleBehavior.serial, downstreamInputs] using downstreamForward.1)
          · exact (boundary .outputData).trans (by
              change (childProposals .downstream).outputs .outputData = _
              simpa [Contracts.Fifo.Cycle.CycleBehavior.serial, downstreamInputs] using downstreamForward.2)
      | ready =>
          change (upstream.cycleBehavior.serial downstream.cycleBehavior).readyRule.Holds
            inputs contractState outputs
          rw [Contracts.Fifo.Cycle.CycleBehavior.readyRule_holds_iff]
          have boundary := satisfies.1
          exact (boundary .inputReady).trans (by
            change (childProposals .upstream).outputs .inputReady = _
            simpa [Contracts.Fifo.Cycle.CycleBehavior.serial, upstreamInputs] using upstreamReady)
    · rfl
  · constructor
    · have nextEq : upstream.certified.cycleContract.stateRule.apply
          upstreamActual (Contracts.Fifo.Cycle.leftState contractState) =
          upstream.cycleBehavior.nextState
          (upstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.leftState contractState) := by
        rw [Contracts.Fifo.Cycle.CertifiedCycleBehavior.certified_stateRule_apply]
        rw [← upstreamActual_eq]
        rfl
      change upstream.certified.stateCorresponds
        (Contracts.Fifo.Cycle.leftState nextContractState) (childProposals .upstream).nextState
      change upstream.certified.stateCorresponds
        (upstream.cycleBehavior.nextState
          (upstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.leftState contractState)) (childProposals .upstream).nextState
      rw [← nextEq]
      exact upstreamNextCorresponds
    · have nextEq : downstream.certified.cycleContract.stateRule.apply
          downstreamActual (Contracts.Fifo.Cycle.rightState contractState) =
          downstream.cycleBehavior.nextState
          (downstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.rightState contractState) := by
        rw [Contracts.Fifo.Cycle.CertifiedCycleBehavior.certified_stateRule_apply]
        rw [← downstreamActual_eq]
        rfl
      change downstream.certified.stateCorresponds
        (Contracts.Fifo.Cycle.rightState nextContractState) (childProposals .downstream).nextState
      change downstream.certified.stateCorresponds
        (downstream.cycleBehavior.nextState
          (downstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.rightState contractState)) (childProposals .downstream).nextState
      rw [← nextEq]
      exact downstreamNextCorresponds

private noncomputable def proofCertification
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.ModuleCycleCertification
      (Contracts.Cycle.Certification.moduleStructure (body signalType) (children upstream downstream))
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract where
  stateCorresponds := stateCorresponds upstream downstream
  hasCorrespondingState := hasCorrespondingState upstream downstream
  hasStructuralResult := hasStructuralResult upstream downstream
  structuralResultUnique := hasAtMostOneSolution upstream downstream
  implements := implements upstream downstream

noncomputable def certification
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.ModuleCycleCertification
      (moduleStructure signalType upstream.moduleStructure downstream.moduleStructure)
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract :=
  (proofCertification upstream downstream).transportStructure
    (moduleStructure_eq upstream downstream).symm

noncomputable def certifiedCycleBehavior
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType where
  cycleBehavior := upstream.cycleBehavior.serial downstream.cycleBehavior
  moduleStructure := moduleStructure signalType upstream.moduleStructure
    downstream.moduleStructure
  certification := certification upstream downstream

end Silean.Composition.FifoSerial

namespace Silean.Composition.FifoSerial.Naming

open Silean Silean.Naming

def serialNamingWith (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) (depth : Nat)
    {upstream downstream : ModuleStructure (Silean.Interfaces.Fifo.ports signalType)}
    (upstreamNaming : ModuleNaming upstream)
    (downstreamNaming : ModuleNaming downstream) :
    ModuleNaming (Composition.FifoSerial.moduleStructure signalType upstream downstream) := by
  unfold Composition.FifoSerial.moduleStructure
  exact .composite
    ⟨"serial_depth_fifo", "structural", [.shape signalType, .natural depth]⟩
    (Silean.Naming.FifoPorts.portsWithNaming signalType typeNaming)
    (fun | .upstream => "upstream" | .downstream => "downstream")
    (fun | .upstream => upstreamNaming | .downstream => downstreamNaming)

end Silean.Composition.FifoSerial.Naming
