import Silean.Contracts.Cycle.CycleImplementation
import Silean.Composition.SignalAdapter

namespace Silean.Composition

/-! Cycle contracts and generic correctness proofs for the stateless splitters
and combiners defined in `SignalAdapter`. -/

inductive SignalComponentRule
  | apply
deriving Enumeration

@[reducible] def signalComponentRuleEnumeration : Enumeration SignalComponentRule where
  values := [.apply]
  nodup := by simp
  locate | .apply => .head

namespace SignalSplitter

def outputRule (splitter : SignalSplitter) :
    Contracts.Cycle.CycleOutputRule splitter.ports emptySignalMap where
  readsInputs := .all splitter.ports.inputs
  writesOutputs := .all splitter.ports.outputs
  target := fun inputs _ => splitter.outputValues inputs

def cycleContract (splitter : SignalSplitter) :
    Contracts.Cycle.ModuleCycleContract splitter.ports where
  state := emptySignalMap
  RuleName := SignalComponentRule
  ruleNames := signalComponentRuleEnumeration
  outputRule | .apply => outputRule splitter
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by
    rw [show signalComponentRuleEnumeration.values = [SignalComponentRule.apply] by rfl]
    simp [outputRule]

theorem outputRule_holds_iff (splitter : SignalSplitter)
    (inputs : splitter.ports.inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : splitter.ports.outputs.Values) :
    splitter.outputRule.Holds inputs state outputs ↔
      outputs = splitter.outputValues inputs := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, outputRule]

private def emptyStateCorresponds (_ : emptySignalMap.Values)
    (_ : emptySignalMap.Values) : Prop := True

private theorem implements (splitter : SignalSplitter) :
    Contracts.Cycle.ImplementsSolutions (.splitter splitter) splitter.cycleContract
      emptyStateCorresponds := by
  intro contractState hierStep corresponds satisfies
  cases hierStep with
  | mk inputs outputs =>
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change splitter.outputRule.Holds inputs contractState outputs
    change outputs = splitter.outputValues inputs at satisfies
    rw [satisfies]
    exact SignalGroup.matches_project _ _
  · rfl

def certified (splitter : SignalSplitter) :
    Contracts.Cycle.ModuleCycleCertified splitter.ports where
  moduleStructure := .splitter splitter
  cycleContract := splitter.cycleContract
  certification := {
    structural := splitter.structuralCertification,
    stateCorresponds := emptyStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp
      splitter.implements }

end SignalSplitter

namespace SignalCombiner

def outputRule (combiner : SignalCombiner) :
    Contracts.Cycle.CycleOutputRule combiner.ports emptySignalMap where
  readsInputs := .all combiner.ports.inputs
  writesOutputs := .all combiner.ports.outputs
  target := fun inputs _ => combiner.outputValues inputs

def cycleContract (combiner : SignalCombiner) :
    Contracts.Cycle.ModuleCycleContract combiner.ports where
  state := emptySignalMap
  RuleName := SignalComponentRule
  ruleNames := signalComponentRuleEnumeration
  outputRule | .apply => outputRule combiner
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by
    rw [show signalComponentRuleEnumeration.values = [SignalComponentRule.apply] by rfl]
    simp [outputRule]

theorem outputRule_holds_iff (combiner : SignalCombiner)
    (inputs : combiner.ports.inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : combiner.ports.outputs.Values) :
    combiner.outputRule.Holds inputs state outputs ↔
      outputs = combiner.outputValues inputs := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, outputRule]

private def emptyStateCorresponds (_ : emptySignalMap.Values)
    (_ : emptySignalMap.Values) : Prop := True

private theorem implements (combiner : SignalCombiner) :
    Contracts.Cycle.ImplementsSolutions (.combiner combiner) combiner.cycleContract
      emptyStateCorresponds := by
  intro contractState hierStep corresponds satisfies
  cases hierStep with
  | mk inputs outputs =>
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change combiner.outputRule.Holds inputs contractState outputs
    change outputs = combiner.outputValues inputs at satisfies
    rw [satisfies]
    exact SignalGroup.matches_project _ _
  · rfl

def certified (combiner : SignalCombiner) :
    Contracts.Cycle.ModuleCycleCertified combiner.ports where
  moduleStructure := .combiner combiner
  cycleContract := combiner.cycleContract
  certification := {
    structural := combiner.structuralCertification,
    stateCorresponds := emptyStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp
      combiner.implements }

end SignalCombiner

end Silean.Composition
