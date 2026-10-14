import Silean.Modules.CarrySaveLayer.Internal.CarrySaveLayerArithmetic
import Silean.Modules.CarrySaveLayer.Internal.CarrySaveLayerStructure
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleRuleSchedules

/-! Direct structural proof of the custom carry-save-layer contract. -/

namespace Silean.Modules.CarrySaveLayer

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (width : Nat) (operandCount : Nat)
    for body width operandCount where
  split := (Internal.splitter width operandCount).certified.certification,
  adder (_group : Fin (groupCount operandCount)) :=
    CarrySaveAdder.certification width,
  combine := (Internal.combiner width operandCount).certified.certification,
  reindex := VectorReindex.certification (.vector width .bit)
    (reducedCount operandCount) (reducedCount operandCount)
    (Internal.interleaveLayout operandCount)

@[reducible] private def childRules (width operandCount : Nat) :
    ModuleStructuralCertification.Layer.ChildRules (body width operandCount) :=
  Contracts.Cycle.Certification.Layer.childStructuralRules
    (body width operandCount) (childContracts width operandCount)

private abbrev splitOccurrence (width operandCount : Nat) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body width operandCount) (childRules width operandCount) :=
  ⟨.split, Composition.SignalComponentRule.apply⟩

private abbrev adderOccurrence (width operandCount : Nat)
    (group : Fin (groupCount operandCount)) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body width operandCount) (childRules width operandCount) :=
  ⟨.adder group, .apply⟩

private abbrev combineOccurrence (width operandCount : Nat) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body width operandCount) (childRules width operandCount) :=
  ⟨.combine, Composition.SignalComponentRule.apply⟩

private abbrev reindexOccurrence (width operandCount : Nat) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body width operandCount) (childRules width operandCount) :=
  ⟨.reindex, .apply⟩

module_complete_schedule completeSchedule (width : Nat) (operandCount : Nat)
    for body width operandCount with childRules width operandCount := from (
    [splitOccurrence width operandCount] ++
    (Enumeration.fin (groupCount operandCount)).values.map
      (adderOccurrence width operandCount) ++
    [combineOccurrence width operandCount,
      reindexOccurrence width operandCount])

/-- Contract-independent structural certification of one compression layer. -/
theorem Internal.structuralCertification (width operandCount : Nat) :
    ModuleStructuralCertification (moduleStructure width operandCount) :=
  (completeSchedule width operandCount).certifyComposite
    (structuralChildren width operandCount)
    (Contracts.Cycle.Certification.Layer.structuralChildren
      (certifiedChildren width operandCount))
    (certifiedChildren_moduleStructure width operandCount)

theorem Internal.contract_of_realization (width operandCount : Nat)
    {step : (moduleStructure width operandCount).Step}
    (realizes : (moduleStructure width operandCount).Realizes step) :
    contract width operandCount step.inputs step.outputs := by
  rcases realizes with ⟨hierStep, satisfies, rfl⟩

  have splitInput : (hierStep.children .split).inputs .value =
      hierStep.inputs .operands := by
    simpa only [wiring, EndpointContext.moduleInput, SignalSource.value] using
      ModuleStructure.child_input satisfies (.split) (.value)
  have splitOutputs : (hierStep.children .split).outputs =
      (Internal.splitter width operandCount).outputValues
        (hierStep.children .split).inputs := by
    exact ModuleStructure.splitter_outputs_of_solution
      (by simpa only [structuralChildren] using
        ModuleStructure.child_isSolution satisfies (.split))
  have splitAt (index : Fin operandCount) :
      (hierStep.children .split).outputs index =
        hierStep.inputs .operands index := by
    calc
      (hierStep.children .split).outputs index =
          (Internal.splitter width operandCount).outputValues
            (hierStep.children .split).inputs index := congrFun splitOutputs index
      _ = (hierStep.children .split).inputs .value index := rfl
      _ = hierStep.inputs .operands index := congrFun splitInput index

  have adderInputA (group : Fin (groupCount operandCount)) :
      (hierStep.children (.adder group)).inputs .iA =
        (hierStep.children .split).outputs
          (Internal.groupedInputIndex operandCount group 0) := by
    simpa only [wiring, EndpointContext.instanceOutput, SignalSource.value] using
      ModuleStructure.child_input satisfies (.adder group) (.iA)
  have adderInputB (group : Fin (groupCount operandCount)) :
      (hierStep.children (.adder group)).inputs .iB =
        (hierStep.children .split).outputs
          (Internal.groupedInputIndex operandCount group 1) := by
    simpa only [wiring, EndpointContext.instanceOutput, SignalSource.value] using
      ModuleStructure.child_input satisfies (.adder group) (.iB)
  have adderInputC (group : Fin (groupCount operandCount)) :
      (hierStep.children (.adder group)).inputs .iC =
        (hierStep.children .split).outputs
          (Internal.groupedInputIndex operandCount group 2) := by
    simpa only [wiring, EndpointContext.instanceOutput, SignalSource.value] using
      ModuleStructure.child_input satisfies (.adder group) (.iC)

  let sums : Fin (groupCount operandCount) → Fin width → Bool :=
    fun group =>
    (hierStep.children (.adder group)).outputs CarrySaveAdder.Output.sum
  let carries : Fin (groupCount operandCount) → Fin width → Bool :=
    fun group =>
    (hierStep.children (.adder group)).outputs CarrySaveAdder.Output.carry
  let remainder : Fin (remainderCount operandCount) → Fin width → Bool :=
    fun index =>
    (hierStep.children .split).outputs
      (Internal.remainderInputIndex operandCount index)

  have groupsPreserve : Internal.GroupsPreserveTotal width operandCount
      (hierStep.inputs .operands) sums carries := by
    intro group
    have childRealizes := ModuleStructure.child_realizes satisfies (.adder group)
    simp only [structuralChildren] at childRealizes
    have equation := CarrySaveAdder.numeric_value_of_realization width childRealizes
    simp only [HierStep.step_inputs, HierStep.step_outputs] at equation
    rw [adderInputA group, adderInputB group, adderInputC group] at equation
    simpa only [sums, carries, splitAt] using equation

  have remainderMatches : Internal.RemainderMatches width operandCount
      (hierStep.inputs .operands) remainder := by
    intro index
    exact splitAt _

  have combineInput (index : Fin (reducedCount operandCount)) :
      (hierStep.children .combine).inputs index =
        Internal.flatten operandCount
          (fun group => (hierStep.children (.adder group)).outputs .sum)
          (fun group => (hierStep.children (.adder group)).outputs .carry)
          (fun rest => (hierStep.children .split).outputs
            (Internal.remainderInputIndex operandCount rest)) index := by
    have equation := ModuleStructure.child_input satisfies (.combine) index
    simp only [wiring] at equation
    rw [Internal.flatten_source_value
      (context := context width operandCount)
      (signalType := .vector width .bit)] at equation
    simpa only [EndpointContext.instanceOutput, SignalSource.value,
      SignalType.vectorComponents, SignalType.Denote] using equation
  have combineOutputs : (hierStep.children .combine).outputs =
      (Internal.combiner width operandCount).outputValues
        (hierStep.children .combine).inputs := by
    exact ModuleStructure.combiner_outputs_of_solution
      (by simpa only [structuralChildren] using
        ModuleStructure.child_isSolution satisfies (.combine))
  have outputArrangement : hierStep.outputs .reduced =
      Internal.interleave operandCount sums carries remainder := by
    have parentOutput : hierStep.outputs .reduced =
        (hierStep.children .reindex).outputs .output := by
      simpa only [wiring, EndpointContext.instanceOutput,
        SignalSource.value] using
        ModuleStructure.parent_output satisfies (.reduced)
    have combinedOutput : (hierStep.children .combine).outputs .value =
        (hierStep.children .combine).inputs := by
      simpa only [Internal.combiner,
        Composition.SignalCombiner.outputValues,
        SignalType.vectorComponents, SignalType.Denote] using
          congrFun combineOutputs .value
    have combinedInputs : (hierStep.children .combine).inputs =
        Internal.flatten operandCount sums carries remainder := by
      funext index
      change (hierStep.children .combine).inputs index =
        Internal.flatten operandCount
          (fun group => (hierStep.children (.adder group)).outputs .sum)
          (fun group => (hierStep.children (.adder group)).outputs .carry)
          (fun rest => (hierStep.children .split).outputs
            (Internal.remainderInputIndex operandCount rest)) index
      exact combineInput index
    have reindexInput : (hierStep.children .reindex).inputs .input =
        (hierStep.children .combine).outputs .value := by
      simpa only [wiring, EndpointContext.instanceOutput,
        SignalSource.value] using
        ModuleStructure.child_input satisfies (.reindex) (.input)
    have reindexRealizes := ModuleStructure.child_realizes satisfies (.reindex)
    simp only [structuralChildren] at reindexRealizes
    have reindexOutput := VectorReindex.output_of_realization
      (.vector width .bit)
      (reducedCount operandCount) (reducedCount operandCount)
      (Internal.interleaveLayout operandCount) reindexRealizes
    simp only [HierStep.step_inputs, HierStep.step_outputs] at reindexOutput
    rw [reindexInput, combinedOutput, combinedInputs] at reindexOutput
    have arrangement := Internal.reindex_flatten
      (α := Fin width → Bool) operandCount sums carries remainder
    exact parentOutput.trans (reindexOutput.trans arrangement)

  change Accepts width operandCount (hierStep.inputs .operands)
    (hierStep.outputs .reduced)
  rw [outputArrangement]
  constructor
  · exact Internal.interleave_preservesTotal width operandCount
      (hierStep.inputs .operands) sums carries remainder
      groupsPreserve remainderMatches
  · exact Internal.interleave_naturalBaseCase width operandCount
      (hierStep.inputs .operands) sums carries remainder remainderMatches

end Silean.Modules.CarrySaveLayer
