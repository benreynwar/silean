import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Naming.PrimitiveNaming
import Silean.Primitives

namespace Silean.Modules.OneEntryFifo.Control

open Silean
open Contracts.Cycle.Certification.Layer

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

@[reducible] def structuralChildren : (child : Instance) →
    ModuleStructure (instancePorts.ports child)
  | .invertValid => .primitive Primitives.not
  | .readyOr => .primitive Primitives.or
  | .updateEq => .primitive Primitives.eq

def moduleStructure : ModuleStructure ports :=
  .composite body structuralChildren

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

@[reducible] def childContracts : Contracts.Cycle.ChildCycleContracts body
  | .invertValid => Primitives.notCycleContract
  | .readyOr => Primitives.orCycleContract
  | .updateEq => Primitives.eqCycleContract

abbrev invertRule : Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.invertValid, Primitives.NotRule.apply⟩
abbrev readyRule : Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.readyOr, Primitives.OrRule.apply⟩
abbrev updateRule : Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.updateEq, Primitives.EqRule.apply⟩

private def scheduleOrders : ScheduleDerivation.RuleScheduleOrders
    body childContracts cycleContract where
  output | .control => [invertRule, readyRule, updateRule]
  state := []

private def derivedRuleSchedules : ScheduleDerivation.DerivedRuleSchedules
    body childContracts cycleContract := by
  derive_rule_schedules scheduleOrders

private abbrev ruleSchedules := derivedRuleSchedules.schedules
private theorem coversChildren : ruleSchedules.CoversChildren :=
  derivedRuleSchedules.coversChildren

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

section LayerCertification

variable (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
  body childContracts)

private theorem implements : Contracts.Cycle.Implements
    (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
    cycleContract (fun _ _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childMatches :=
    Contracts.Cycle.Certification.Layer.childSolutionsMatchContracts_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
      (fun child => by cases child <;> exact SignalMap.emptyValues)
      (by intro child; cases child <;>
        change Subsingleton emptySignalMap.Values <;> infer_instance)
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change controlRule.Holds inputs contractState proposal.outputs
    rw [controlRule_holds_iff]
    rcases proposal with ⟨outputs, children⟩
    have invertEvaluates := (childMatches .invertValid).1
    have readyEvaluates := (childMatches .readyOr).1
    have updateEvaluates := (childMatches .updateEq).1
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

end LayerCertification

/-- The control wiring implements its contract for any children satisfying the
three declared primitive contracts. -/
noncomputable opaque certifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer body childContracts cycleContract :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    ruleSchedules coversChildren (fun _ _ _ => True)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) implements

@[reducible] noncomputable def certifiedChildren :
    Contracts.Cycle.Certification.Layer.ChildStructures body childContracts
  | .invertValid => Primitives.notCertified.certifiedStructure
  | .readyOr => Primitives.orCertified.certifiedStructure
  | .updateEq => Primitives.eqCertified.certifiedStructure

noncomputable opaque certification :
    Contracts.Cycle.ModuleCycleCertification moduleStructure cycleContract :=
  certifiedLayer.certifyComposite structuralChildren certifiedChildren (by
    intro child
    cases child <;> rfl)

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
  unfold Modules.OneEntryFifo.Control.moduleStructure
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
