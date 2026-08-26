import Silean2.Modules.FifoBehavior
import Silean2.CertifiedSchedule

namespace Silean2.Modules.SerialFifo

open Silean2
open Fifo

inductive Instance
  | upstream
  | downstream
deriving Enumeration

@[reducible] def instances (signalType : SignalType) : Instances :=
  EnumeratedMap.of Instance fun _ => OneEntryFifo.ports signalType

@[reducible] def context (signalType : SignalType) : EndpointContext where
  ports := OneEntryFifo.ports signalType
  instances := instances signalType

def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instances where
  moduleOutput
    | .outputValid => (context signalType).instanceOutput .downstream .outputValid
    | .outputData => (context signalType).instanceOutput .downstream .outputData
    | .inputReady => (context signalType).instanceOutput .upstream .inputReady
  instanceInput
    | .upstream, .inputValid => (context signalType).moduleInput .inputValid
    | .upstream, .inputData => (context signalType).moduleInput .inputData
    | .upstream, .outputReady =>
        (context signalType).instanceOutput .downstream .inputReady
    | .downstream, .inputValid =>
        (context signalType).instanceOutput .upstream .outputValid
    | .downstream, .inputData =>
        (context signalType).instanceOutput .upstream .outputData
    | .downstream, .outputReady => (context signalType).moduleInput .outputReady

@[reducible] def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

def moduleStructure (signalType : SignalType)
    (upstream downstream : ModuleStructure (OneEntryFifo.ports signalType)) :
    ModuleStructure (OneEntryFifo.ports signalType) :=
  .composite (body signalType) fun
    | .upstream => upstream
    | .downstream => downstream

@[reducible] noncomputable def children
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    Certified.Children (body signalType)
  | .upstream => upstream.certified
  | .downstream => downstream.certified

abbrev upstreamForward (upstream downstream : Fifo.CertifiedBehavior signalType) :
    Certified.RuleOccurrence (children upstream downstream) :=
  ⟨.upstream, OneEntryFifo.Rule.forward⟩

abbrev upstreamReady (upstream downstream : Fifo.CertifiedBehavior signalType) :
    Certified.RuleOccurrence (children upstream downstream) :=
  ⟨.upstream, OneEntryFifo.Rule.ready⟩

abbrev downstreamForward (upstream downstream : Fifo.CertifiedBehavior signalType) :
    Certified.RuleOccurrence (children upstream downstream) :=
  ⟨.downstream, OneEntryFifo.Rule.forward⟩

abbrev downstreamReady (upstream downstream : Fifo.CertifiedBehavior signalType) :
    Certified.RuleOccurrence (children upstream downstream) :=
  ⟨.downstream, OneEntryFifo.Rule.ready⟩

@[simp] theorem upstreamForward_reads
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    (upstreamForward upstream downstream).reads = [.inputValid, .inputData] := rfl
@[simp] theorem upstreamForward_writes
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    (upstreamForward upstream downstream).writes = [.outputValid, .outputData] := rfl
@[simp] theorem upstreamReady_reads
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    (upstreamReady upstream downstream).reads = [.outputReady] := rfl
@[simp] theorem upstreamReady_writes
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    (upstreamReady upstream downstream).writes = [.inputReady] := rfl
@[simp] theorem downstreamForward_reads
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    (downstreamForward upstream downstream).reads = [.inputValid, .inputData] := rfl
@[simp] theorem downstreamForward_writes
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    (downstreamForward upstream downstream).writes = [.outputValid, .outputData] := rfl
@[simp] theorem downstreamReady_reads
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    (downstreamReady upstream downstream).reads = [.outputReady] := rfl
@[simp] theorem downstreamReady_writes
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    (downstreamReady upstream downstream).writes = [.inputReady] := rfl

def forwardSchedule (upstream downstream : Fifo.CertifiedBehavior signalType) :
    Certified.OutputSchedule (body signalType) (children upstream downstream)
      (upstream.behavior.serial downstream.behavior).cycleContract .forward :=
  .call (upstreamForward upstream downstream)
    (by
      intro input member
      cases input with
      | inputValid | inputData =>
          simp [Certified.sourceAvailable, body, wiring, context,
            EndpointContext.moduleInput]
      | outputReady => simp at member)
    (by simp)
  (.call (downstreamForward upstream downstream)
    (by
      intro input member
      cases input with
      | inputValid | inputData =>
          exact ⟨OneEntryFifo.Rule.forward, by simp, by simp⟩
      | outputReady => simp at member)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | outputValid | outputData =>
        exact ⟨OneEntryFifo.Rule.forward, by simp, by simp⟩
    | inputReady => simp at member)))

def readySchedule (upstream downstream : Fifo.CertifiedBehavior signalType) :
    Certified.OutputSchedule (body signalType) (children upstream downstream)
      (upstream.behavior.serial downstream.behavior).cycleContract .ready :=
  .call (downstreamReady upstream downstream)
    (by
      intro input member
      cases input with
      | outputReady =>
          simp [Certified.sourceAvailable, body, wiring, context,
            EndpointContext.moduleInput]
      | inputValid | inputData => simp at member)
    (by simp)
  (.call (upstreamReady upstream downstream)
    (by
      intro input member
      cases input with
      | outputReady => exact ⟨OneEntryFifo.Rule.ready, by simp, by simp⟩
      | inputValid | inputData => simp at member)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | inputReady => exact ⟨OneEntryFifo.Rule.ready, by simp, by simp⟩
    | outputValid | outputData => simp at member)))

def stateSchedule (upstream downstream : Fifo.CertifiedBehavior signalType) :
    Certified.StateSchedule (body signalType) (children upstream downstream) :=
  .call (upstreamForward upstream downstream)
    (by
      intro input member
      cases input with
      | inputValid | inputData =>
          simp [Certified.sourceAvailable, body, wiring, context,
            EndpointContext.moduleInput]
      | outputReady => simp at member) (by simp)
  (.call (downstreamForward upstream downstream)
    (by
      intro input member
      cases input with
      | inputValid | inputData =>
          exact ⟨OneEntryFifo.Rule.forward, by simp, by simp⟩
      | outputReady => simp at member)
    (by simp)
  (.call (downstreamReady upstream downstream)
    (by
      intro input member
      cases input with
      | outputReady =>
          simp [Certified.sourceAvailable, body, wiring, context,
            EndpointContext.moduleInput]
      | inputValid | inputData => simp at member) (by simp)
  (.call (upstreamReady upstream downstream)
    (by
      intro input member
      cases input with
      | outputReady => exact ⟨OneEntryFifo.Rule.ready, by simp, by simp⟩
      | inputValid | inputData => simp at member)
    (by simp)
  (.done trivial))))

def ruleSchedules (upstream downstream : Fifo.CertifiedBehavior signalType) :
    Certified.RuleSchedules (body signalType) (children upstream downstream)
      (upstream.behavior.serial downstream.behavior).cycleContract where
  output
    | .forward => forwardSchedule upstream downstream
    | .ready => readySchedule upstream downstream
  state := stateSchedule upstream downstream

theorem coversChildren (upstream downstream : Fifo.CertifiedBehavior signalType) :
    (ruleSchedules upstream downstream).CoversChildren := by
  intro child rule
  cases child with
  | upstream =>
      change OneEntryFifo.Rule at rule
      cases rule with
      | forward =>
          apply Certified.RuleSchedules.Combined.add_includes
          change upstreamForward upstream downstream ∈
            (stateSchedule upstream downstream).finalAvailability
          simp [stateSchedule, Certified.Schedule.finalAvailability]
      | ready =>
          apply Certified.RuleSchedules.Combined.add_includes
          change upstreamReady upstream downstream ∈
            (stateSchedule upstream downstream).finalAvailability
          simp [stateSchedule, Certified.Schedule.finalAvailability]
  | downstream =>
      change OneEntryFifo.Rule at rule
      cases rule with
      | forward =>
          apply Certified.RuleSchedules.Combined.add_includes
          change downstreamForward upstream downstream ∈
            (stateSchedule upstream downstream).finalAvailability
          simp [stateSchedule, Certified.Schedule.finalAvailability]
      | ready =>
          apply Certified.RuleSchedules.Combined.add_includes
          change downstreamReady upstream downstream ∈
            (stateSchedule upstream downstream).finalAvailability
          simp [stateSchedule, Certified.Schedule.finalAvailability]

theorem hasAtMostOneSolution
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    (Certified.moduleStructure (body signalType)
      (children upstream downstream)).HasAtMostOneSolution :=
  (ruleSchedules upstream downstream).hasAtMostOneSolution
    (coversChildren upstream downstream)

theorem moduleStructure_eq
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    moduleStructure signalType upstream.moduleStructure downstream.moduleStructure =
      Certified.moduleStructure (body signalType) (children upstream downstream) := by
  unfold moduleStructure Certified.moduleStructure
  congr
  funext child
  cases child <;> rfl

def upstreamInputs (upstream downstream : Fifo.Behavior signalType)
    (inputs : (OneEntryFifo.ports signalType).inputs.Values)
    (_upstreamState : upstream.state.Values)
    (downstreamState : downstream.state.Values) :
    (OneEntryFifo.ports signalType).inputs.Values
  | .inputValid => inputs .inputValid
  | .inputData => inputs .inputData
  | .outputReady => downstream.ready (inputs .outputReady) downstreamState

def downstreamInputs (upstream downstream : Fifo.Behavior signalType)
    (inputs : (OneEntryFifo.ports signalType).inputs.Values)
    (upstreamState : upstream.state.Values)
    (_downstreamState : downstream.state.Values) :
    (OneEntryFifo.ports signalType).inputs.Values
  | .inputValid => (upstream.forward (inputs .inputValid) (inputs .inputData)
      upstreamState).1
  | .inputData => (upstream.forward (inputs .inputValid) (inputs .inputData)
      upstreamState).2
  | .outputReady => inputs .outputReady

def stateCorresponds (upstream downstream : Fifo.CertifiedBehavior signalType)
    (contractState : (upstream.behavior.serial downstream.behavior).state.Values)
    (structuralState : (Certified.moduleStructure (body signalType)
      (children upstream downstream)).State) : Prop :=
  upstream.certified.stateCorresponds (Fifo.leftState contractState)
      (structuralState .upstream) ∧
    downstream.certified.stateCorresponds (Fifo.rightState contractState)
      (structuralState .downstream)

theorem hasCorrespondingState
    (upstream downstream : Fifo.CertifiedBehavior signalType)
    (structuralState : (Certified.moduleStructure (body signalType)
      (children upstream downstream)).State) :
    ∃ contractState, stateCorresponds upstream downstream contractState structuralState := by
  rcases upstream.certified.hasCorrespondingState (structuralState .upstream) with
    ⟨upstreamState, upstreamCorresponds⟩
  rcases downstream.certified.hasCorrespondingState (structuralState .downstream) with
    ⟨downstreamState, downstreamCorresponds⟩
  exact ⟨Fifo.combineState upstreamState downstreamState,
    ⟨upstreamCorresponds, downstreamCorresponds⟩⟩

theorem hasStructuralResult
    (upstream downstream : Fifo.CertifiedBehavior signalType)
    (inputs : (OneEntryFifo.ports signalType).inputs.Values)
    (structuralState : (Certified.moduleStructure (body signalType)
      (children upstream downstream)).State) :
    ∃ proposal, (Certified.moduleStructure (body signalType)
      (children upstream downstream)).IsSolution inputs structuralState proposal := by
  rcases upstream.certified.hasCorrespondingState (structuralState .upstream) with
    ⟨upstreamState, upstreamCorresponds⟩
  rcases downstream.certified.hasCorrespondingState (structuralState .downstream) with
    ⟨downstreamState, downstreamCorresponds⟩
  let upstreamInput := upstreamInputs upstream.behavior downstream.behavior
    inputs upstreamState downstreamState
  let downstreamInput := downstreamInputs upstream.behavior downstream.behavior
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
  have upstreamForward := upstream.behavior.evaluate_forward upstreamInput upstreamState
  have upstreamReady := upstream.behavior.evaluate_ready upstreamInput upstreamState
  have downstreamForward := downstream.behavior.evaluate_forward downstreamInput downstreamState
  have downstreamReady := downstream.behavior.evaluate_ready downstreamInput downstreamState
  dsimp only at upstreamForward upstreamReady downstreamForward downstreamReady
  have upstreamMatch : upstreamProposal.outputs =
      (upstream.behavior.cycleContract.evaluate upstreamInput upstreamState).1 :=
    upstreamMatches.1
  have downstreamMatch : downstreamProposal.outputs =
      (downstream.behavior.cycleContract.evaluate downstreamInput downstreamState).1 :=
    downstreamMatches.1
  rw [← upstreamMatch] at upstreamForward upstreamReady
  rw [← downstreamMatch] at downstreamForward downstreamReady
  let childProposals : (name : Instance) → ProposedValues
      (Certified.childStructure (children upstream downstream) name)
    | .upstream => upstreamProposal
    | .downstream => downstreamProposal
  let outputs : (OneEntryFifo.ports signalType).outputs.Values := fun
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
            (Certified.childStructure (children upstream downstream)) inputs
            childProposals .upstream) (structuralState .upstream) upstreamProposal
        rw [show ProposedValues.childInputs (body signalType)
            (Certified.childStructure (children upstream downstream)) inputs
            childProposals .upstream = upstreamInput by
          funext port
          cases port with
          | inputValid | inputData => rfl
          | outputReady =>
              change downstreamProposal.outputs .inputReady = _
              exact downstreamReady]
        exact upstreamSatisfies
    | downstream =>
        change downstream.moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType)
            (Certified.childStructure (children upstream downstream)) inputs
            childProposals .downstream) (structuralState .downstream)
              downstreamProposal
        rw [show ProposedValues.childInputs (body signalType)
            (Certified.childStructure (children upstream downstream)) inputs
            childProposals .downstream = downstreamInput by
          funext port
          cases port with
          | inputValid => exact upstreamForward.1
          | inputData => exact upstreamForward.2
          | outputReady => rfl]
        exact downstreamSatisfies

theorem implements
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    Implements (Certified.moduleStructure (body signalType)
      (children upstream downstream))
      (upstream.behavior.serial downstream.behavior).cycleContract
      (stateCorresponds upstream downstream) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have upstreamImpl := Certified.childImplements (children upstream downstream)
    inputs structuralState proposal satisfies .upstream
      (Fifo.leftState contractState) corresponds.1
  have downstreamImpl := Certified.childImplements (children upstream downstream)
    inputs structuralState proposal satisfies .downstream
      (Fifo.rightState contractState) corresponds.2
  rcases proposal with ⟨outputs, childProposals⟩
  rcases upstreamImpl with ⟨upstreamNext, upstreamEvaluates, upstreamNextCorresponds⟩
  rcases downstreamImpl with
    ⟨downstreamNext, downstreamEvaluates, downstreamNextCorresponds⟩
  let upstreamActual := ProposedValues.childInputs (body signalType)
    (Certified.childStructure (children upstream downstream)) inputs
      childProposals .upstream
  let downstreamActual := ProposedValues.childInputs (body signalType)
    (Certified.childStructure (children upstream downstream)) inputs
      childProposals .downstream
  have upstreamForward := (upstream.behavior.forwardRule_holds_iff upstreamActual
    (Fifo.leftState contractState) (childProposals .upstream).outputs).mp
      (upstreamEvaluates.1 .forward)
  have upstreamReady := (upstream.behavior.readyRule_holds_iff upstreamActual
    (Fifo.leftState contractState) (childProposals .upstream).outputs).mp
      (upstreamEvaluates.1 .ready)
  have downstreamForward := (downstream.behavior.forwardRule_holds_iff downstreamActual
    (Fifo.rightState contractState) (childProposals .downstream).outputs).mp
      (downstreamEvaluates.1 .forward)
  have downstreamReady := (downstream.behavior.readyRule_holds_iff downstreamActual
    (Fifo.rightState contractState) (childProposals .downstream).outputs).mp
      (downstreamEvaluates.1 .ready)
  change (childProposals .upstream).outputs .outputValid =
      (upstream.behavior.forward (inputs .inputValid) (inputs .inputData)
        (Fifo.leftState contractState)).1 ∧
    (childProposals .upstream).outputs .outputData =
      (upstream.behavior.forward (inputs .inputValid) (inputs .inputData)
        (Fifo.leftState contractState)).2 at upstreamForward
  change (childProposals .downstream).outputs .inputReady =
    downstream.behavior.ready (inputs .outputReady)
      (Fifo.rightState contractState) at downstreamReady
  have upstreamActual_eq : upstreamActual =
      upstreamInputs upstream.behavior downstream.behavior inputs
        (Fifo.leftState contractState) (Fifo.rightState contractState) := by
    funext port
    cases port with
    | inputValid | inputData => rfl
    | outputReady =>
        change (childProposals .downstream).outputs .inputReady = _
        exact downstreamReady
  have downstreamActual_eq : downstreamActual =
      downstreamInputs upstream.behavior downstream.behavior inputs
        (Fifo.leftState contractState) (Fifo.rightState contractState) := by
    funext port
    cases port with
    | inputValid =>
        change (childProposals .upstream).outputs .outputValid = _
        exact upstreamForward.1
    | inputData =>
        change (childProposals .upstream).outputs .outputData = _
        exact upstreamForward.2
    | outputReady => rfl
  rw [upstreamActual_eq] at upstreamReady
  rw [downstreamActual_eq] at downstreamForward
  let nextContractState :=
    (upstream.behavior.serial downstream.behavior).nextState inputs contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule with
      | forward =>
          change (upstream.behavior.serial downstream.behavior).forwardRule.Holds
            inputs contractState outputs
          rw [Fifo.Behavior.forwardRule_holds_iff]
          have boundary := satisfies.1
          constructor
          · exact (boundary .outputValid).trans (by
              change (childProposals .downstream).outputs .outputValid = _
              simpa [Fifo.Behavior.serial, downstreamInputs] using downstreamForward.1)
          · exact (boundary .outputData).trans (by
              change (childProposals .downstream).outputs .outputData = _
              simpa [Fifo.Behavior.serial, downstreamInputs] using downstreamForward.2)
      | ready =>
          change (upstream.behavior.serial downstream.behavior).readyRule.Holds
            inputs contractState outputs
          rw [Fifo.Behavior.readyRule_holds_iff]
          have boundary := satisfies.1
          exact (boundary .inputReady).trans (by
            change (childProposals .upstream).outputs .inputReady = _
            simpa [Fifo.Behavior.serial, upstreamInputs] using upstreamReady)
    · rfl
  · constructor
    · have nextEq : upstreamNext = upstream.behavior.nextState
          (upstreamInputs upstream.behavior downstream.behavior inputs
            (Fifo.leftState contractState) (Fifo.rightState contractState))
          (Fifo.leftState contractState) := by
        rw [← upstreamActual_eq]
        exact upstreamEvaluates.2
      change upstream.certified.stateCorresponds
        (Fifo.leftState nextContractState) (childProposals .upstream).nextState
      change upstream.certified.stateCorresponds
        (upstream.behavior.nextState
          (upstreamInputs upstream.behavior downstream.behavior inputs
            (Fifo.leftState contractState) (Fifo.rightState contractState))
          (Fifo.leftState contractState)) (childProposals .upstream).nextState
      rw [← nextEq]
      exact upstreamNextCorresponds
    · have nextEq : downstreamNext = downstream.behavior.nextState
          (downstreamInputs upstream.behavior downstream.behavior inputs
            (Fifo.leftState contractState) (Fifo.rightState contractState))
          (Fifo.rightState contractState) := by
        rw [← downstreamActual_eq]
        exact downstreamEvaluates.2
      change downstream.certified.stateCorresponds
        (Fifo.rightState nextContractState) (childProposals .downstream).nextState
      change downstream.certified.stateCorresponds
        (downstream.behavior.nextState
          (downstreamInputs upstream.behavior downstream.behavior inputs
            (Fifo.leftState contractState) (Fifo.rightState contractState))
          (Fifo.rightState contractState)) (childProposals .downstream).nextState
      rw [← nextEq]
      exact downstreamNextCorresponds

noncomputable def proofCertification
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    ModuleCycleCertification
      (Certified.moduleStructure (body signalType) (children upstream downstream))
      (upstream.behavior.serial downstream.behavior).cycleContract where
  stateCorresponds := stateCorresponds upstream downstream
  hasCorrespondingState := hasCorrespondingState upstream downstream
  hasStructuralResult := hasStructuralResult upstream downstream
  structuralResultUnique := hasAtMostOneSolution upstream downstream
  implements := implements upstream downstream

noncomputable def certification
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    ModuleCycleCertification
      (moduleStructure signalType upstream.moduleStructure downstream.moduleStructure)
      (upstream.behavior.serial downstream.behavior).cycleContract :=
  (proofCertification upstream downstream).transportStructure
    (moduleStructure_eq upstream downstream).symm

noncomputable def certifiedBehavior
    (upstream downstream : Fifo.CertifiedBehavior signalType) :
    Fifo.CertifiedBehavior signalType where
  behavior := upstream.behavior.serial downstream.behavior
  moduleStructure := moduleStructure signalType upstream.moduleStructure
    downstream.moduleStructure
  certification := certification upstream downstream

end Silean2.Modules.SerialFifo
