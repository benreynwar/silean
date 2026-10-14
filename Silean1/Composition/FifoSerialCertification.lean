import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.FifoSerialComposition
import Silean.Contracts.Cycle.CycleLayerConstruction

namespace Silean.Composition.FifoSerial

open Silean
open Silean.Authoring
open Contracts.Fifo.Cycle
open Contracts.Cycle.Certification.Layer

/-! # Serial FIFO certification

Structural certification for the generic two-child serial FIFO layer. This is
a public composition operation rather than the verification file of one fixed
module: `certifiedLayer`, `certification`, and `certifiedCycleBehavior` are its
supported results. The proof is parametric in certified child implementations
and uses their cycle contracts rather than their internal structures.
-/

@[reducible] private def childContracts
    (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :
    Contracts.Cycle.ChildCycleContracts (body signalType)
  | .upstream => upstream.cycleContract
  | .downstream => downstream.cycleContract

module_rule_schedules derivedRuleSchedules
    (upstream : Contracts.Fifo.Cycle.CycleBehavior signalType)
    (downstream : Contracts.Fifo.Cycle.CycleBehavior signalType)
    for body signalType with childContracts upstream downstream
    implementing (upstream.serial downstream).cycleContract where
  output
    | .forward => [.upstream => Contracts.Fifo.Cycle.Rule.forward,
        .downstream => Contracts.Fifo.Cycle.Rule.forward]
    | .ready => [.downstream => Contracts.Fifo.Cycle.Rule.ready,
        .upstream => Contracts.Fifo.Cycle.Rule.ready]
  state := [.upstream => Contracts.Fifo.Cycle.Rule.forward,
    .downstream => Contracts.Fifo.Cycle.Rule.forward,
    .downstream => Contracts.Fifo.Cycle.Rule.ready,
    .upstream => Contracts.Fifo.Cycle.Rule.ready]

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
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType) layerChildren)
      (upstream.serial downstream).cycleContract
      (stateCorresponds upstream downstream layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have upstreamMatch := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    (body := body signalType) layerChildren hierStep satisfies .upstream
      (Contracts.Fifo.Cycle.leftState contractState) corresponds.1
  have downstreamMatch := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    (body := body signalType) layerChildren hierStep satisfies .downstream
      (Contracts.Fifo.Cycle.rightState contractState) corresponds.2
  let inputs := hierStep.inputs
  let outputs := hierStep.outputs
  let childSteps := hierStep.children
  let upstreamActual := (body signalType).wiring.childInputValues
    inputs hierStep.childOutputs .upstream
  let downstreamActual := (body signalType).wiring.childInputValues
    inputs hierStep.childOutputs .downstream
  have upstreamForward := (upstream.forwardRule_holds_iff upstreamActual
    (Contracts.Fifo.Cycle.leftState contractState) (childSteps .upstream).outputs).mp
      (upstreamMatch.ruleHolds .forward)
  have upstreamReady := (upstream.readyRule_holds_iff upstreamActual
    (Contracts.Fifo.Cycle.leftState contractState) (childSteps .upstream).outputs).mp
      (upstreamMatch.ruleHolds .ready)
  have downstreamForward := (downstream.forwardRule_holds_iff downstreamActual
    (Contracts.Fifo.Cycle.rightState contractState) (childSteps .downstream).outputs).mp
      (downstreamMatch.ruleHolds .forward)
  have downstreamReady := (downstream.readyRule_holds_iff downstreamActual
    (Contracts.Fifo.Cycle.rightState contractState) (childSteps .downstream).outputs).mp
      (downstreamMatch.ruleHolds .ready)
  change (childSteps .upstream).outputs .outputValid =
      (upstream.forward (inputs .inputValid) (inputs .inputData)
        (Contracts.Fifo.Cycle.leftState contractState)).1 ∧
    (childSteps .upstream).outputs .outputData =
      (upstream.forward (inputs .inputValid) (inputs .inputData)
        (Contracts.Fifo.Cycle.leftState contractState)).2 at upstreamForward
  change (childSteps .downstream).outputs .inputReady =
    downstream.ready (inputs .outputReady)
      (Contracts.Fifo.Cycle.rightState contractState) at downstreamReady
  have upstreamActual_eq : upstreamActual =
      CycleBehavior.serialUpstreamInputs upstream downstream inputs
        (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState) := by
    funext port
    cases port with
    | inputValid | inputData | reset => rfl
    | outputReady =>
        change (childSteps .downstream).outputs .inputReady = _
        exact downstreamReady
  have downstreamActual_eq : downstreamActual =
      CycleBehavior.serialDownstreamInputs upstream downstream inputs
        (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState) := by
    funext port
    cases port with
    | inputValid =>
        change (childSteps .upstream).outputs .outputValid = _
        exact upstreamForward.1
    | inputData =>
        change (childSteps .upstream).outputs .outputData = _
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
              change (childSteps .downstream).outputs .outputValid = _
              simpa [Contracts.Fifo.Cycle.CycleBehavior.serial, CycleBehavior.serialDownstreamInputs] using downstreamForward.1)
          · exact (boundary .outputData).trans (by
              change (childSteps .downstream).outputs .outputData = _
              simpa [Contracts.Fifo.Cycle.CycleBehavior.serial, CycleBehavior.serialDownstreamInputs] using downstreamForward.2)
      | ready =>
          change (upstream.serial downstream).readyRule.Holds
            inputs contractState outputs
          rw [Contracts.Fifo.Cycle.CycleBehavior.readyRule_holds_iff]
          have boundary := satisfies.1
          exact (boundary .inputReady).trans (by
            change (childSteps .upstream).outputs .inputReady = _
            simpa [Contracts.Fifo.Cycle.CycleBehavior.serial, CycleBehavior.serialUpstreamInputs] using upstreamReady)
    · rfl
  · constructor
    · have nextEq : upstream.cycleContract.stateRule.apply
          upstreamActual (Contracts.Fifo.Cycle.leftState contractState) =
          upstream.nextState
          (CycleBehavior.serialUpstreamInputs upstream downstream inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.leftState contractState) := by
        rw [upstream.cycleContract_stateRule_apply, upstreamActual_eq]
        rfl
      change (layerChildren .upstream).certification.stateCorresponds
        (Contracts.Fifo.Cycle.leftState nextContractState)
          (HierStep.nextState (layerChildren .upstream).moduleStructure
            (childSteps .upstream))
      change (layerChildren .upstream).certification.stateCorresponds
        (upstream.nextState
          (CycleBehavior.serialUpstreamInputs upstream downstream inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.leftState contractState))
          (HierStep.nextState (layerChildren .upstream).moduleStructure
            (childSteps .upstream))
      rw [← nextEq]
      exact upstreamMatch.nextCorresponds
    · have nextEq : downstream.cycleContract.stateRule.apply
          downstreamActual (Contracts.Fifo.Cycle.rightState contractState) =
          downstream.nextState
          (CycleBehavior.serialDownstreamInputs upstream downstream inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.rightState contractState) := by
        rw [downstream.cycleContract_stateRule_apply, downstreamActual_eq]
        rfl
      change (layerChildren .downstream).certification.stateCorresponds
        (Contracts.Fifo.Cycle.rightState nextContractState)
          (HierStep.nextState (layerChildren .downstream).moduleStructure
            (childSteps .downstream))
      change (layerChildren .downstream).certification.stateCorresponds
        (downstream.nextState
          (CycleBehavior.serialDownstreamInputs upstream downstream inputs
            (Contracts.Fifo.Cycle.leftState contractState) (Contracts.Fifo.Cycle.rightState contractState))
          (Contracts.Fifo.Cycle.rightState contractState))
          (HierStep.nextState (layerChildren .downstream).moduleStructure
            (childSteps .downstream))
      rw [← nextEq]
      exact downstreamMatch.nextCorresponds

end LayerCertification

/-- Serial wiring implements serial composition for any two child hierarchies
satisfying the supplied FIFO cycle contracts. -/
noncomputable opaque certifiedLayer
    (upstream downstream : Contracts.Fifo.Cycle.CycleBehavior signalType) :
    Contracts.Cycle.ModuleCycleCertifiedLayer
      (body signalType) (childContracts upstream downstream)
      (upstream.serial downstream).cycleContract :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (derivedRuleSchedules upstream downstream).schedules
    (derivedRuleSchedules upstream downstream).coversChildren
    (stateCorresponds upstream downstream)
    (hasCorrespondingState upstream downstream) (implements upstream downstream)

@[reducible] private noncomputable def certifiedChildren
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (body signalType) (childContracts upstream.cycleBehavior downstream.cycleBehavior)
  | .upstream => upstream.certified.certifiedStructure
  | .downstream => downstream.certified.certifiedStructure

/-- Instantiate the generic serial layer with two concrete certified FIFO
cycle behaviors. -/
noncomputable def certification
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Cycle.ModuleCycleCertification
      (moduleStructure signalType upstream.moduleStructure downstream.moduleStructure)
      (upstream.cycleBehavior.serial downstream.cycleBehavior).cycleContract :=
  (certifiedLayer upstream.cycleBehavior downstream.cycleBehavior).certifyComposite
    (fun | .upstream => upstream.moduleStructure | .downstream => downstream.moduleStructure)
    (certifiedChildren upstream downstream) (by intro child; cases child <;> rfl)

/-- Package serial composition as a certified FIFO cycle behavior, ready for
further serial composition or logical FIFO refinement. -/
noncomputable def certifiedCycleBehavior
    (upstream downstream : Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType) :
    Contracts.Fifo.Cycle.CertifiedCycleBehavior signalType where
  cycleBehavior := upstream.cycleBehavior.serial downstream.cycleBehavior
  moduleStructure := moduleStructure signalType upstream.moduleStructure
    downstream.moduleStructure
  certification := certification upstream downstream

end Silean.Composition.FifoSerial
