import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation

namespace Silean.Modules

open Silean
open Contracts.Cycle.Certification.Layer

inductive NamedTupleAdapterRule
  | apply
deriving Enumeration

namespace NamedTupleCombiner

def outputRule (signals : SignalMap) :
    Contracts.Cycle.CycleOutputRule (ports signals) emptySignalMap where
  readsInputs := .all signals
  writesOutputs := .all (Composition.aggregateSignalMap signals.tupleType)
  target := fun inputs _ => fun | .value => combinedValue signals inputs

@[reducible] def cycleContract (signals : SignalMap) :
    Contracts.Cycle.ModuleCycleContract (ports signals) where
  state := emptySignalMap
  RuleName := NamedTupleAdapterRule
  ruleNames := inferInstance
  outputRule | .apply => outputRule signals
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (signals : SignalMap)
    (inputs : (ports signals).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signals).outputs.Values) :
    (outputRule signals).Holds inputs state outputs ↔
      outputs .value = combinedValue signals inputs := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .value
  · intro equal
    funext label
    cases label
    exact equal

@[reducible] private def adapter (signals : SignalMap) : Composition.SignalCombiner :=
  .tuple signals.tupleFields

@[reducible] def childContracts (signals : SignalMap) :
    Contracts.Cycle.ChildCycleContracts (body signals)
  | .adapter => (adapter signals).cycleContract

private abbrev occurrence (signals : SignalMap) :
    RuleOccurrence (body signals) (childContracts signals) :=
  ⟨.adapter, Composition.SignalComponentRule.apply⟩

private def scheduleOrders (signals : SignalMap) :
    ScheduleDerivation.RuleScheduleOrders (body signals)
      (childContracts signals) (cycleContract signals) where
  output | .apply => [occurrence signals]
  state := []

private def derivedSchedules (signals : SignalMap) :
    ScheduleDerivation.DerivedRuleSchedules (body signals)
      (childContracts signals) (cycleContract signals) := by
  derive_rule_schedules (scheduleOrders signals)

@[reducible] def structuralChildren (signals : SignalMap) :
    ChildStructures (body signals) (childContracts signals)
  | .adapter => ⟨.combiner (adapter signals), (adapter signals).certified.certification⟩

private def stateCorresponds (signals : SignalMap)
    (_ : emptySignalMap.Values)
    (_ : (moduleStructure signals).State) : Prop := True

private theorem implements (signals : SignalMap) : Contracts.Cycle.Implements
    (moduleStructure signals) (cycleContract signals)
    (stateCorresponds signals) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  letI : Subsingleton (childContracts signals .adapter).state.Values := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have childMatch := childSolutionMatchesContract_of_subsingletonState
    (structuralChildren signals) inputs structuralState proposal satisfies
    .adapter SignalMap.emptyValues
  have childValue := ((adapter signals).outputRule_holds_iff _ _ _).mp
    (childMatch.1.1 Composition.SignalComponentRule.apply)
  have childInputsEqual :
      ProposedValues.childInputs (body signals)
          (fun name => (structuralChildren signals name).moduleStructure)
          inputs proposal.2 .adapter =
        signals.allSelection.valueAt inputs := by
    funext position
    exact adapterInputValue signals inputs
      (fun name => (proposal.2 name).outputs) position
  rw [childInputsEqual] at childValue
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change proposal.outputs .value =
      signals.tupleFields.assemble (signals.allSelection.valueAt inputs)
    exact (boundary .value).trans (congrFun childValue .value)
  · rfl

def certification (signals : SignalMap) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signals)
      (cycleContract signals) where
  stateCorresponds := stateCorresponds signals
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := (derivedSchedules signals).schedules.hasSolution
    (derivedSchedules signals).coversChildren (structuralChildren signals)
  structuralResultUnique := (derivedSchedules signals).schedules.hasAtMostOneSolution
    (derivedSchedules signals).coversChildren (structuralChildren signals)
  implements := implements signals

end NamedTupleCombiner

namespace NamedTupleSplitter

def outputRule (signals : SignalMap) :
    Contracts.Cycle.CycleOutputRule (ports signals) emptySignalMap where
  readsInputs := .all (Composition.aggregateSignalMap signals.tupleType)
  writesOutputs := .all signals
  target := fun inputs _ => splitValue signals (inputs .value)

@[reducible] def cycleContract (signals : SignalMap) :
    Contracts.Cycle.ModuleCycleContract (ports signals) where
  state := emptySignalMap
  RuleName := NamedTupleAdapterRule
  ruleNames := inferInstance
  outputRule | .apply => outputRule signals
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by
    rw [show (inferInstance : Enumeration NamedTupleAdapterRule).values =
      [NamedTupleAdapterRule.apply] by rfl]
    simp [outputRule]

@[simp] theorem outputRule_holds_iff (signals : SignalMap)
    (inputs : (ports signals).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports signals).outputs.Values) :
    (outputRule signals).Holds inputs state outputs ↔
      outputs = splitValue signals (inputs .value) := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds]

@[reducible] private def adapter (signals : SignalMap) : Composition.SignalSplitter :=
  .tuple signals.tupleFields

@[reducible] def childContracts (signals : SignalMap) :
    Contracts.Cycle.ChildCycleContracts (body signals)
  | .adapter => (adapter signals).cycleContract

private abbrev occurrence (signals : SignalMap) :
    RuleOccurrence (body signals) (childContracts signals) :=
  ⟨.adapter, Composition.SignalComponentRule.apply⟩

private noncomputable def outputSchedule (signals : SignalMap) :
    OutputSchedule (body signals) (childContracts signals)
      (cycleContract signals) .apply := by
  apply Schedule.call (occurrence signals)
  · intro input member
    cases input
    simpa [body, wiring, context, occurrence, RuleOccurrence.reads,
      childContracts, adapter, cycleContract, outputRule]
  · simp [occurrence]
  · apply Schedule.done
    intro output member
    have available : sourceAvailable
        (body := body signals) (childContracts := childContracts signals)
        (fun input => input ∈
          ((cycleContract signals).outputRule .apply).readsInputs.labels)
        [occurrence signals]
        ((context signals).instanceOutput .adapter
          (signals.tuplePosition output)) := by
      refine sourceAvailable_of_instanceOutput
        (rule := (occurrence signals).rule) (by simp) ?_
      have positionMember : signals.tuplePosition output ∈
          signals.tupleFields.positions.values :=
        ListIndex.get_eq
        (signals.tupleFields.positions.locate (signals.tuplePosition output)) ▸
          List.get_mem _ _
      simpa [RuleOccurrence.writes, occurrence, childContracts, adapter,
        Composition.SignalSplitter.cycleContract,
        Composition.SignalSplitter.outputRule] using positionMember
    have castAvailable :=
      (sourceAvailable_castType (body := body signals)
        (childContracts := childContracts signals) _ _
        (signals.typeAt_tuplePosition output)
        ((context signals).instanceOutput .adapter
          (signals.tuplePosition output))).2 available
    simpa only [body, wiring] using castAvailable

private noncomputable def ruleSchedules (signals : SignalMap) :
    RuleSchedules (body signals) (childContracts signals)
      (cycleContract signals) where
  output | .apply => outputSchedule signals
  state := .done (by
    intro child input member
    cases child
    change input ∈ (SignalGroup.empty _).labels at member
    simp at member)

private theorem coversChildren (signals : SignalMap) :
    (ruleSchedules signals).CoversChildren := by
  apply RuleSchedules.coversChildren_of_outputMembership
  intro child rule
  cases child
  cases rule
  refine ⟨.apply, ?_⟩
  change occurrence signals ∈
    ((ruleSchedules signals).output .apply).finalAvailability
  unfold ruleSchedules outputSchedule
  simp

@[reducible] def structuralChildren (signals : SignalMap) :
    ChildStructures (body signals) (childContracts signals)
  | .adapter => ⟨.splitter (adapter signals), (adapter signals).certified.certification⟩

private def stateCorresponds (signals : SignalMap)
    (_ : emptySignalMap.Values)
    (_ : (moduleStructure signals).State) : Prop := True

private theorem implements (signals : SignalMap) : Contracts.Cycle.Implements
    (moduleStructure signals) (cycleContract signals)
    (stateCorresponds signals) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  letI : Subsingleton (childContracts signals .adapter).state.Values := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have childMatch := childSolutionMatchesContract_of_subsingletonState
    (structuralChildren signals) inputs structuralState proposal satisfies
    .adapter SignalMap.emptyValues
  have childValue := ((adapter signals).outputRule_holds_iff _ _ _).mp
    (childMatch.1.1 Composition.SignalComponentRule.apply)
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    funext label
    calc
      proposal.1 label =
          ((body signals).wiring.moduleOutput label).value inputs
            (fun name => (proposal.2 name).outputs) := boundary label
      _ = signals.typeAt_tuplePosition label ▸
          (proposal.2 .adapter).outputs (signals.tuplePosition label) :=
        moduleOutputValue signals inputs
          (fun name => (proposal.2 name).outputs) label
      _ = signals.typeAt_tuplePosition label ▸
          (adapter signals).outputValues
            (ProposedValues.childInputs (body signals)
              (fun name => (structuralChildren signals name).moduleStructure)
              inputs proposal.2 .adapter) (signals.tuplePosition label) := by
        exact castOutput_congr signals label _ _ childValue
      _ = splitValue signals (inputs .value) label := by rfl
  · rfl

def certification (signals : SignalMap) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signals)
      (cycleContract signals) where
  stateCorresponds := stateCorresponds signals
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := (ruleSchedules signals).hasSolution
    (coversChildren signals) (structuralChildren signals)
  structuralResultUnique := (ruleSchedules signals).hasAtMostOneSolution
    (coversChildren signals) (structuralChildren signals)
  implements := implements signals

end NamedTupleSplitter
end Silean.Modules
