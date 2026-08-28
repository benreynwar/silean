import Silean.ModuleCycleCertified
import Silean.SignalAdapter

namespace Silean

inductive SignalComponentRule
  | apply
deriving Enumeration

@[reducible] def signalComponentRuleEnumeration : Enumeration SignalComponentRule where
  values := [.apply]
  nodup := by simp
  locate | .apply => .head

namespace SignalSplitter

def outputRule (splitter : SignalSplitter) :
    CycleOutputRule splitter.ports emptySignalMap
      { inputTypes := .ofList splitter.ports.inputs.types
        outputTypes := .ofList splitter.ports.outputs.types } where
  readsInputs := splitter.ports.inputs.allSelection
  writesOutputs := splitter.ports.outputs.allSelection
  target := fun packed _ => splitter.ports.outputs.allSelection.project
    (splitter.outputValues (splitter.ports.inputs.unpack packed))

def cycleContract (splitter : SignalSplitter) :
    ModuleCycleContract splitter.ports where
  state := emptySignalMap
  RuleName := SignalComponentRule
  ruleNames := signalComponentRuleEnumeration
  outputRule | .apply => ⟨_, outputRule splitter⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by
    rw [show signalComponentRuleEnumeration.values = [SignalComponentRule.apply] by rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change splitter.ports.outputs.allSelection.labels.Perm
      splitter.ports.outputs.labels.values
    rw [SignalMap.allSelection_labels]

theorem outputRule_holds_iff (splitter : SignalSplitter)
    (inputs : splitter.ports.inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : splitter.ports.outputs.Values) :
    splitter.outputRule.Holds inputs state outputs ↔
      outputs = splitter.outputValues inputs := by
  simp only [CycleOutputRule.Holds, outputRule]
  rw [splitter.ports.inputs.unpack_project]
  exact SignalSelection.allSelection_matches_project_iff _ _ _

private def emptyStateCorresponds (_ : emptySignalMap.Values)
    (_ : emptySignalMap.Values) : Prop := True

private theorem implements (splitter : SignalSplitter) :
    Implements (.splitter splitter) splitter.cycleContract
      emptyStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change splitter.outputRule.Holds inputs contractState proposal
    simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
      SignalSplitter.IsSolution] at satisfies
    rw [satisfies]
    simp only [outputRule, CycleOutputRule.Holds]
    rw [splitter.ports.inputs.unpack_project]
    exact splitter.ports.outputs.allSelection.matches_project _
  · rfl

def certified (splitter : SignalSplitter) :
    ModuleCycleCertified splitter.ports where
  moduleStructure := .splitter splitter
  cycleContract := splitter.cycleContract
  certification := {
    stateCorresponds := emptyStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := fun inputs _ =>
      ⟨ProposedValues.splitter (splitter.outputValues inputs), rfl⟩,
    structuralResultUnique := splitter.hasAtMostOneSolution,
    implements := splitter.implements }

end SignalSplitter

namespace SignalCombiner

def outputRule (combiner : SignalCombiner) :
    CycleOutputRule combiner.ports emptySignalMap
      { inputTypes := .ofList combiner.ports.inputs.types
        outputTypes := .ofList combiner.ports.outputs.types } where
  readsInputs := combiner.ports.inputs.allSelection
  writesOutputs := combiner.ports.outputs.allSelection
  target := fun packed _ => combiner.ports.outputs.allSelection.project
    (combiner.outputValues (combiner.ports.inputs.unpack packed))

def cycleContract (combiner : SignalCombiner) :
    ModuleCycleContract combiner.ports where
  state := emptySignalMap
  RuleName := SignalComponentRule
  ruleNames := signalComponentRuleEnumeration
  outputRule | .apply => ⟨_, outputRule combiner⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by
    rw [show signalComponentRuleEnumeration.values = [SignalComponentRule.apply] by rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change combiner.ports.outputs.allSelection.labels.Perm
      combiner.ports.outputs.labels.values
    rw [SignalMap.allSelection_labels]

theorem outputRule_holds_iff (combiner : SignalCombiner)
    (inputs : combiner.ports.inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : combiner.ports.outputs.Values) :
    combiner.outputRule.Holds inputs state outputs ↔
      outputs = combiner.outputValues inputs := by
  simp only [CycleOutputRule.Holds, outputRule]
  rw [combiner.ports.inputs.unpack_project]
  exact SignalSelection.allSelection_matches_project_iff _ _ _

private def emptyStateCorresponds (_ : emptySignalMap.Values)
    (_ : emptySignalMap.Values) : Prop := True

private theorem implements (combiner : SignalCombiner) :
    Implements (.combiner combiner) combiner.cycleContract
      emptyStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change combiner.outputRule.Holds inputs contractState proposal
    simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
      SignalCombiner.IsSolution] at satisfies
    rw [satisfies]
    simp only [outputRule, CycleOutputRule.Holds]
    rw [combiner.ports.inputs.unpack_project]
    exact combiner.ports.outputs.allSelection.matches_project _
  · rfl

def certified (combiner : SignalCombiner) :
    ModuleCycleCertified combiner.ports where
  moduleStructure := .combiner combiner
  cycleContract := combiner.cycleContract
  certification := {
    stateCorresponds := emptyStateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := fun inputs _ =>
      ⟨ProposedValues.combiner (combiner.outputValues inputs), rfl⟩,
    structuralResultUnique := combiner.hasAtMostOneSolution,
    implements := combiner.implements }

end SignalCombiner

end Silean
