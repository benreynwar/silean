import Silean.Contracts.Fifo.FifoCycleBehavior
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation

namespace Silean.Composition.FifoSerial

open Silean
open Contracts.Fifo.Cycle
open Contracts.Cycle.Certification.Layer

/-! Connects two FIFO implementations in series. The upstream FIFO accepts the
external input, the downstream FIFO drives the external output, and their
valid/ready boundaries are connected internally. -/

inductive Instance
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

@[reducible] private def childContracts
    (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :
    Contracts.Cycle.ChildCycleContracts (body signalType)
  | .upstream => upstream.cycleContract
  | .downstream => downstream.cycleContract

private abbrev upstreamForward (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts upstream downstream) :=
  ⟨.upstream, Contracts.Fifo.Cycle.Rule.forward⟩

private abbrev upstreamReady (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts upstream downstream) :=
  ⟨.upstream, Contracts.Fifo.Cycle.Rule.ready⟩

private abbrev downstreamForward (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts upstream downstream) :=
  ⟨.downstream, Contracts.Fifo.Cycle.Rule.forward⟩

private abbrev downstreamReady (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts upstream downstream) :=
  ⟨.downstream, Contracts.Fifo.Cycle.Rule.ready⟩

private def scheduleOrders
    (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :
    ScheduleDerivation.RuleScheduleOrders (body signalType)
      (childContracts upstream downstream) (upstream.serial downstream).cycleContract where
  output
    | .forward => [upstreamForward upstream downstream,
        downstreamForward upstream downstream]
    | .ready => [downstreamReady upstream downstream,
        upstreamReady upstream downstream]
  state := [upstreamForward upstream downstream, downstreamForward upstream downstream,
    downstreamReady upstream downstream, upstreamReady upstream downstream]

private def derivedRuleSchedules
    (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :
    ScheduleDerivation.DerivedRuleSchedules (body signalType)
      (childContracts upstream downstream) (upstream.serial downstream).cycleContract := by
  derive_rule_schedules (scheduleOrders upstream downstream)

private abbrev ruleSchedules
    (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :=
  (derivedRuleSchedules upstream downstream).schedules

private theorem coversChildren
    (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :
    (ruleSchedules upstream downstream).CoversChildren :=
  (derivedRuleSchedules upstream downstream).coversChildren

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

section LayerCertification

variable (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body signalType) (childContracts upstream downstream))

private def stateCorresponds
    (contractState : (upstream.serial downstream).state.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body signalType) layerChildren).State) : Prop :=
  (layerChildren .upstream).certification.stateCorresponds
      (Contracts.Fifo.Cycle.leftState contractState)
      (structuralState .upstream) ∧
    (layerChildren .downstream).certification.stateCorresponds
      (Contracts.Fifo.Cycle.rightState contractState)
      (structuralState .downstream)

private theorem hasCorrespondingState
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body signalType) layerChildren).State) :
    ∃ contractState,
      stateCorresponds upstream downstream layerChildren contractState structuralState := by
  rcases (layerChildren .upstream).certification.hasCorrespondingState
      (structuralState .upstream) with
    ⟨upstreamState, upstreamCorresponds⟩
  rcases (layerChildren .downstream).certification.hasCorrespondingState
      (structuralState .downstream) with
    ⟨downstreamState, downstreamCorresponds⟩
  exact ⟨Contracts.Fifo.Cycle.combineState upstreamState downstreamState,
    ⟨upstreamCorresponds, downstreamCorresponds⟩⟩

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType) layerChildren)
      (upstream.serial downstream).cycleContract
      (stateCorresponds upstream downstream layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have upstreamMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren
    inputs structuralState proposal satisfies .upstream
      (Contracts.Fifo.Cycle.leftState contractState) corresponds.1
  have downstreamMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren
    inputs structuralState proposal satisfies .downstream
      (Contracts.Fifo.Cycle.rightState contractState) corresponds.2
  rcases proposal with ⟨outputs, childProposals⟩
  rcases upstreamMatches with ⟨upstreamEvaluates, upstreamNextCorresponds⟩
  rcases downstreamMatches with ⟨downstreamEvaluates, downstreamNextCorresponds⟩
  let upstreamActual := ProposedValues.childInputs (body signalType)
    (fun child => (layerChildren child).moduleStructure) inputs
      childProposals .upstream
  let downstreamActual := ProposedValues.childInputs (body signalType)
    (fun child => (layerChildren child).moduleStructure) inputs
      childProposals .downstream
  have upstreamForward := (upstream.forwardRule_holds_iff upstreamActual
    (Contracts.Fifo.Cycle.leftState contractState) (childProposals .upstream).outputs).mp
      (upstreamEvaluates.1 .forward)
  have upstreamReady := (upstream.readyRule_holds_iff upstreamActual
    (Contracts.Fifo.Cycle.leftState contractState) (childProposals .upstream).outputs).mp
      (upstreamEvaluates.1 .ready)
  have downstreamForward := (downstream.forwardRule_holds_iff downstreamActual
    (Contracts.Fifo.Cycle.rightState contractState) (childProposals .downstream).outputs).mp
      (downstreamEvaluates.1 .forward)
  have downstreamReady := (downstream.readyRule_holds_iff downstreamActual
    (Contracts.Fifo.Cycle.rightState contractState) (childProposals .downstream).outputs).mp
      (downstreamEvaluates.1 .ready)
  change (childProposals .upstream).outputs .outputValid =
      (upstream.forward (inputs .inputValid) (inputs .inputData)
        (Contracts.Fifo.Cycle.leftState contractState)).1 ∧
    (childProposals .upstream).outputs .outputData =
      (upstream.forward (inputs .inputValid) (inputs .inputData)
        (Contracts.Fifo.Cycle.leftState contractState)).2 at upstreamForward
  change (childProposals .downstream).outputs .inputReady =
    downstream.ready (inputs .outputReady)
      (Contracts.Fifo.Cycle.rightState contractState) at downstreamReady
  have upstreamActual_eq : upstreamActual =
      upstreamInputs upstream downstream inputs
        (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState) := by
    funext port
    cases port with
    | inputValid | inputData | reset => rfl
    | outputReady =>
        change (childProposals .downstream).outputs .inputReady = _
        exact downstreamReady
  have downstreamActual_eq : downstreamActual =
      downstreamInputs upstream downstream inputs
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
    (upstream.serial downstream).nextState inputs contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule with
      | forward =>
          change (upstream.serial downstream).forwardRule.Holds
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
          change (upstream.serial downstream).readyRule.Holds
            inputs contractState outputs
          rw [Contracts.Fifo.Cycle.CycleBehavior.readyRule_holds_iff]
          have boundary := satisfies.1
          exact (boundary .inputReady).trans (by
            change (childProposals .upstream).outputs .inputReady = _
            simpa [Contracts.Fifo.Cycle.CycleBehavior.serial, upstreamInputs] using upstreamReady)
    · rfl
  · constructor
    · have nextEq : upstream.cycleContract.stateRule.apply
          upstreamActual (Contracts.Fifo.Cycle.leftState contractState) =
          upstream.nextState
          (upstreamInputs upstream downstream inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.leftState contractState) := by
        rw [upstream.cycleContract_stateRule_apply, upstreamActual_eq]
        rfl
      change (layerChildren .upstream).certification.stateCorresponds
        (Contracts.Fifo.Cycle.leftState nextContractState) (childProposals .upstream).nextState
      change (layerChildren .upstream).certification.stateCorresponds
        (upstream.nextState
          (upstreamInputs upstream downstream inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.leftState contractState)) (childProposals .upstream).nextState
      rw [← nextEq]
      exact upstreamNextCorresponds
    · have nextEq : downstream.cycleContract.stateRule.apply
          downstreamActual (Contracts.Fifo.Cycle.rightState contractState) =
          downstream.nextState
          (downstreamInputs upstream downstream inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.rightState contractState) := by
        rw [downstream.cycleContract_stateRule_apply, downstreamActual_eq]
        rfl
      change (layerChildren .downstream).certification.stateCorresponds
        (Contracts.Fifo.Cycle.rightState nextContractState) (childProposals .downstream).nextState
      change (layerChildren .downstream).certification.stateCorresponds
        (downstream.nextState
          (downstreamInputs upstream downstream inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.rightState contractState)) (childProposals .downstream).nextState
      rw [← nextEq]
      exact downstreamNextCorresponds

end LayerCertification

/-- Serial wiring implements serial composition for any two child hierarchies
satisfying the supplied FIFO cycle contracts. -/
noncomputable opaque certifiedLayer
    (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :
    Contracts.Cycle.ModuleCycleCertifiedLayer
      (body signalType) (childContracts upstream downstream)
      (upstream.serial downstream).cycleContract :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules upstream downstream) (coversChildren upstream downstream)
    (stateCorresponds upstream downstream)
    (hasCorrespondingState upstream downstream) (implements upstream downstream)

@[reducible] private noncomputable def certifiedChildren
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (body signalType) (childContracts upstream.cycleBehavior downstream.cycleBehavior)
  | .upstream => upstream.certified.certifiedStructure
  | .downstream => downstream.certified.certifiedStructure

noncomputable def certification
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.ModuleCycleCertification
      (moduleStructure signalType upstream.moduleStructure downstream.moduleStructure)
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract :=
  (certifiedLayer upstream.cycleBehavior downstream.cycleBehavior).certifyComposite
    (fun | .upstream => upstream.moduleStructure | .downstream => downstream.moduleStructure)
    (certifiedChildren upstream downstream) (by intro child; cases child <;> rfl)

noncomputable def certifiedCycleBehavior
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType where
  cycleBehavior := upstream.cycleBehavior.serial downstream.cycleBehavior
  moduleStructure := moduleStructure signalType upstream.moduleStructure
    downstream.moduleStructure
  certification := certification upstream downstream

end Silean.Composition.FifoSerial
