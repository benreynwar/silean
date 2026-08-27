import Silean2.Modules.FifoCycleBehavior
import Silean2.CertifiedSchedule

namespace Silean2.Modules.SerialFifo

open Silean2
open Fifo

private inductive Instance
  | upstream
  | downstream
deriving Enumeration

@[reducible] private def instances (signalType : SignalType) : Instances :=
  EnumeratedMap.of Instance fun _ => Fifo.ports signalType

@[reducible] private def context (signalType : SignalType) : EndpointContext where
  ports := Fifo.ports signalType
  instances := instances signalType

private def wiring (signalType : SignalType) :
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

@[reducible] private def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

def moduleStructure (signalType : SignalType)
    (upstream downstream : ModuleStructure (Fifo.ports signalType)) :
    ModuleStructure (Fifo.ports signalType) :=
  .composite (body signalType) fun
    | .upstream => upstream
    | .downstream => downstream

@[reducible] private noncomputable def children
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    Certified.Children (body signalType)
  | .upstream => upstream.certified
  | .downstream => downstream.certified

private abbrev upstreamForward (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    Certified.RuleOccurrence (children upstream downstream) :=
  ⟨.upstream, Fifo.Rule.forward⟩

private abbrev upstreamReady (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    Certified.RuleOccurrence (children upstream downstream) :=
  ⟨.upstream, Fifo.Rule.ready⟩

private abbrev downstreamForward (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    Certified.RuleOccurrence (children upstream downstream) :=
  ⟨.downstream, Fifo.Rule.forward⟩

private abbrev downstreamReady (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    Certified.RuleOccurrence (children upstream downstream) :=
  ⟨.downstream, Fifo.Rule.ready⟩

@[simp] private theorem upstreamForward_reads
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    (upstreamForward upstream downstream).reads = [.inputValid, .inputData] := rfl
@[simp] private theorem upstreamForward_writes
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    (upstreamForward upstream downstream).writes = [.outputValid, .outputData] := rfl
@[simp] private theorem upstreamReady_reads
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    (upstreamReady upstream downstream).reads = [.outputReady] := rfl
@[simp] private theorem upstreamReady_writes
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    (upstreamReady upstream downstream).writes = [.inputReady] := rfl
@[simp] private theorem downstreamForward_reads
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    (downstreamForward upstream downstream).reads = [.inputValid, .inputData] := rfl
@[simp] private theorem downstreamForward_writes
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    (downstreamForward upstream downstream).writes = [.outputValid, .outputData] := rfl
@[simp] private theorem downstreamReady_reads
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    (downstreamReady upstream downstream).reads = [.outputReady] := rfl
@[simp] private theorem downstreamReady_writes
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    (downstreamReady upstream downstream).writes = [.inputReady] := rfl

private def forwardSchedule (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    Certified.OutputSchedule (body signalType) (children upstream downstream)
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract .forward :=
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
          exact ⟨Fifo.Rule.forward, by simp, by simp⟩
      | outputReady => simp at member)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | outputValid | outputData =>
        exact ⟨Fifo.Rule.forward, by simp, by simp⟩
    | inputReady => simp at member)))

private def readySchedule (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    Certified.OutputSchedule (body signalType) (children upstream downstream)
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract .ready :=
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
      | outputReady => exact ⟨Fifo.Rule.ready, by simp, by simp⟩
      | inputValid | inputData => simp at member)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | inputReady => exact ⟨Fifo.Rule.ready, by simp, by simp⟩
    | outputValid | outputData => simp at member)))

private def stateSchedule (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
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
          exact ⟨Fifo.Rule.forward, by simp, by simp⟩
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
      | outputReady => exact ⟨Fifo.Rule.ready, by simp, by simp⟩
      | inputValid | inputData => simp at member)
    (by simp)
  (.done (by
    intro child input member
    cases child with
    | upstream =>
        cases input with
        | inputValid | inputData => trivial
        | outputReady => exact ⟨Fifo.Rule.ready, by simp, by simp⟩
    | downstream =>
        cases input with
        | inputValid | inputData =>
            exact ⟨Fifo.Rule.forward, by simp, by simp⟩
        | outputReady => trivial)))))

private def ruleSchedules (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    Certified.RuleSchedules (body signalType) (children upstream downstream)
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract where
  output
    | .forward => forwardSchedule upstream downstream
    | .ready => readySchedule upstream downstream
  state := stateSchedule upstream downstream

private theorem coversChildren (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    (ruleSchedules upstream downstream).CoversChildren := by
  intro child rule
  cases child with
  | upstream =>
      change Fifo.Rule at rule
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
      change Fifo.Rule at rule
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

private theorem hasAtMostOneSolution
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    (Certified.moduleStructure (body signalType)
      (children upstream downstream)).HasAtMostOneSolution :=
  (ruleSchedules upstream downstream).hasAtMostOneSolution
    (coversChildren upstream downstream)

private theorem moduleStructure_eq
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    moduleStructure signalType upstream.moduleStructure downstream.moduleStructure =
      Certified.moduleStructure (body signalType) (children upstream downstream) := by
  unfold moduleStructure Certified.moduleStructure
  congr
  funext child
  cases child <;> rfl

private def upstreamInputs (upstream downstream : Fifo.CycleBehavior signalType)
    (inputs : (Fifo.ports signalType).inputs.Values)
    (_upstreamState : upstream.state.Values)
    (downstreamState : downstream.state.Values) :
    (Fifo.ports signalType).inputs.Values
  | .inputValid => inputs .inputValid
  | .inputData => inputs .inputData
  | .outputReady => downstream.ready (inputs .outputReady) downstreamState

private def downstreamInputs (upstream downstream : Fifo.CycleBehavior signalType)
    (inputs : (Fifo.ports signalType).inputs.Values)
    (upstreamState : upstream.state.Values)
    (_downstreamState : downstream.state.Values) :
    (Fifo.ports signalType).inputs.Values
  | .inputValid => (upstream.forward (inputs .inputValid) (inputs .inputData)
      upstreamState).1
  | .inputData => (upstream.forward (inputs .inputValid) (inputs .inputData)
      upstreamState).2
  | .outputReady => inputs .outputReady

private def stateCorresponds (upstream downstream : Fifo.CertifiedCycleBehavior signalType)
    (contractState : (upstream.cycleBehavior.serial downstream.cycleBehavior).state.Values)
    (structuralState : (Certified.moduleStructure (body signalType)
      (children upstream downstream)).State) : Prop :=
  upstream.certified.stateCorresponds (Fifo.leftState contractState)
      (structuralState .upstream) ∧
    downstream.certified.stateCorresponds (Fifo.rightState contractState)
      (structuralState .downstream)

private theorem hasCorrespondingState
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType)
    (structuralState : (Certified.moduleStructure (body signalType)
      (children upstream downstream)).State) :
    ∃ contractState, stateCorresponds upstream downstream contractState structuralState := by
  rcases upstream.certified.hasCorrespondingState (structuralState .upstream) with
    ⟨upstreamState, upstreamCorresponds⟩
  rcases downstream.certified.hasCorrespondingState (structuralState .downstream) with
    ⟨downstreamState, downstreamCorresponds⟩
  exact ⟨Fifo.combineState upstreamState downstreamState,
    ⟨upstreamCorresponds, downstreamCorresponds⟩⟩

private theorem hasStructuralResult
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType)
    (inputs : (Fifo.ports signalType).inputs.Values)
    (structuralState : (Certified.moduleStructure (body signalType)
      (children upstream downstream)).State) :
    ∃ proposal, (Certified.moduleStructure (body signalType)
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
      (Certified.childStructure (children upstream downstream) name)
    | .upstream => upstreamProposal
    | .downstream => downstreamProposal
  let outputs : (Fifo.ports signalType).outputs.Values := fun
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

private theorem implements
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    Implements (Certified.moduleStructure (body signalType)
      (children upstream downstream))
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract
      (stateCorresponds upstream downstream) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have upstreamMatches := Certified.childSolutionMatchesContract
    (children upstream downstream)
    inputs structuralState proposal satisfies .upstream
      (Fifo.leftState contractState) corresponds.1
  have downstreamMatches := Certified.childSolutionMatchesContract
    (children upstream downstream)
    inputs structuralState proposal satisfies .downstream
      (Fifo.rightState contractState) corresponds.2
  rcases proposal with ⟨outputs, childProposals⟩
  rcases upstreamMatches with ⟨upstreamEvaluates, upstreamNextCorresponds⟩
  rcases downstreamMatches with ⟨downstreamEvaluates, downstreamNextCorresponds⟩
  let upstreamActual := ProposedValues.childInputs (body signalType)
    (Certified.childStructure (children upstream downstream)) inputs
      childProposals .upstream
  let downstreamActual := ProposedValues.childInputs (body signalType)
    (Certified.childStructure (children upstream downstream)) inputs
      childProposals .downstream
  have upstreamForward := (upstream.cycleBehavior.forwardRule_holds_iff upstreamActual
    (Fifo.leftState contractState) (childProposals .upstream).outputs).mp
      (upstreamEvaluates.1 .forward)
  have upstreamReady := (upstream.cycleBehavior.readyRule_holds_iff upstreamActual
    (Fifo.leftState contractState) (childProposals .upstream).outputs).mp
      (upstreamEvaluates.1 .ready)
  have downstreamForward := (downstream.cycleBehavior.forwardRule_holds_iff downstreamActual
    (Fifo.rightState contractState) (childProposals .downstream).outputs).mp
      (downstreamEvaluates.1 .forward)
  have downstreamReady := (downstream.cycleBehavior.readyRule_holds_iff downstreamActual
    (Fifo.rightState contractState) (childProposals .downstream).outputs).mp
      (downstreamEvaluates.1 .ready)
  change (childProposals .upstream).outputs .outputValid =
      (upstream.cycleBehavior.forward (inputs .inputValid) (inputs .inputData)
        (Fifo.leftState contractState)).1 ∧
    (childProposals .upstream).outputs .outputData =
      (upstream.cycleBehavior.forward (inputs .inputValid) (inputs .inputData)
        (Fifo.leftState contractState)).2 at upstreamForward
  change (childProposals .downstream).outputs .inputReady =
    downstream.cycleBehavior.ready (inputs .outputReady)
      (Fifo.rightState contractState) at downstreamReady
  have upstreamActual_eq : upstreamActual =
      upstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
        (Fifo.leftState contractState) (Fifo.rightState contractState) := by
    funext port
    cases port with
    | inputValid | inputData => rfl
    | outputReady =>
        change (childProposals .downstream).outputs .inputReady = _
        exact downstreamReady
  have downstreamActual_eq : downstreamActual =
      downstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
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
    (upstream.cycleBehavior.serial downstream.cycleBehavior).nextState inputs contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule with
      | forward =>
          change (upstream.cycleBehavior.serial downstream.cycleBehavior).forwardRule.Holds
            inputs contractState outputs
          rw [Fifo.CycleBehavior.forwardRule_holds_iff]
          have boundary := satisfies.1
          constructor
          · exact (boundary .outputValid).trans (by
              change (childProposals .downstream).outputs .outputValid = _
              simpa [Fifo.CycleBehavior.serial, downstreamInputs] using downstreamForward.1)
          · exact (boundary .outputData).trans (by
              change (childProposals .downstream).outputs .outputData = _
              simpa [Fifo.CycleBehavior.serial, downstreamInputs] using downstreamForward.2)
      | ready =>
          change (upstream.cycleBehavior.serial downstream.cycleBehavior).readyRule.Holds
            inputs contractState outputs
          rw [Fifo.CycleBehavior.readyRule_holds_iff]
          have boundary := satisfies.1
          exact (boundary .inputReady).trans (by
            change (childProposals .upstream).outputs .inputReady = _
            simpa [Fifo.CycleBehavior.serial, upstreamInputs] using upstreamReady)
    · rfl
  · constructor
    · have nextEq : upstream.certified.cycleContract.stateRule.apply
          upstreamActual (Fifo.leftState contractState) =
          upstream.cycleBehavior.nextState
          (upstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
            (Fifo.leftState contractState) (Fifo.rightState contractState))
          (Fifo.leftState contractState) := by
        rw [Fifo.CertifiedCycleBehavior.certified_stateRule_apply]
        rw [← upstreamActual_eq]
        rfl
      change upstream.certified.stateCorresponds
        (Fifo.leftState nextContractState) (childProposals .upstream).nextState
      change upstream.certified.stateCorresponds
        (upstream.cycleBehavior.nextState
          (upstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
            (Fifo.leftState contractState) (Fifo.rightState contractState))
          (Fifo.leftState contractState)) (childProposals .upstream).nextState
      rw [← nextEq]
      exact upstreamNextCorresponds
    · have nextEq : downstream.certified.cycleContract.stateRule.apply
          downstreamActual (Fifo.rightState contractState) =
          downstream.cycleBehavior.nextState
          (downstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
            (Fifo.leftState contractState) (Fifo.rightState contractState))
          (Fifo.rightState contractState) := by
        rw [Fifo.CertifiedCycleBehavior.certified_stateRule_apply]
        rw [← downstreamActual_eq]
        rfl
      change downstream.certified.stateCorresponds
        (Fifo.rightState nextContractState) (childProposals .downstream).nextState
      change downstream.certified.stateCorresponds
        (downstream.cycleBehavior.nextState
          (downstreamInputs upstream.cycleBehavior downstream.cycleBehavior inputs
            (Fifo.leftState contractState) (Fifo.rightState contractState))
          (Fifo.rightState contractState)) (childProposals .downstream).nextState
      rw [← nextEq]
      exact downstreamNextCorresponds

private noncomputable def proofCertification
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    ModuleCycleCertification
      (Certified.moduleStructure (body signalType) (children upstream downstream))
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract where
  stateCorresponds := stateCorresponds upstream downstream
  hasCorrespondingState := hasCorrespondingState upstream downstream
  hasStructuralResult := hasStructuralResult upstream downstream
  structuralResultUnique := hasAtMostOneSolution upstream downstream
  implements := implements upstream downstream

noncomputable def certification
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    ModuleCycleCertification
      (moduleStructure signalType upstream.moduleStructure downstream.moduleStructure)
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract :=
  (proofCertification upstream downstream).transportStructure
    (moduleStructure_eq upstream downstream).symm

noncomputable def certifiedCycleBehavior
    (upstream downstream : Fifo.CertifiedCycleBehavior signalType) :
    Fifo.CertifiedCycleBehavior signalType where
  cycleBehavior := upstream.cycleBehavior.serial downstream.cycleBehavior
  moduleStructure := moduleStructure signalType upstream.moduleStructure
    downstream.moduleStructure
  certification := certification upstream downstream

end Silean2.Modules.SerialFifo

namespace Silean2.Modules.SerialFifo.Naming

open Silean2 Silean2.Naming

def serialNamingWith (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) (depth : Nat)
    {upstream downstream : ModuleStructure (Modules.Fifo.ports signalType)}
    (upstreamNaming : ModuleNaming upstream)
    (downstreamNaming : ModuleNaming downstream) :
    ModuleNaming (Modules.SerialFifo.moduleStructure signalType upstream downstream) := by
  unfold Modules.SerialFifo.moduleStructure
  exact .composite
    ⟨"fifo", "structural", [.shape signalType, .natural depth]⟩
    (Modules.OneEntryFifo.Naming.portsWithNaming signalType typeNaming)
    (fun | .upstream => "upstream" | .downstream => "downstream")
    (fun | .upstream => upstreamNaming | .downstream => downstreamNaming)

end Silean2.Modules.SerialFifo.Naming
