import Silean.Examples.PicoRV.Decoder.DecoderResolveStageStructure
import Silean.Contracts.Cycle.CycleScheduleDerivation

namespace Silean.Examples.PicoRV.Decoder.ResolveStage

open Silean
open Silean.Examples.PicoRV.Decoder
open Contracts.Cycle.Certification.Layer

/-! ## Structural schedules

The explicit orders are the only module-specific scheduling information.
`derive_rule_schedules` checks their dependencies and constructs both the
proof-bearing schedules and their child-rule coverage proof.
-/

private abbrev occurrence (child : Instance)
    (rule : (childContracts child).RuleName) : RuleOccurrence body childContracts :=
  ⟨child, rule⟩

private abbrev pseudoRule := occurrence .pseudoInverter Primitives.NotRule.apply
private abbrev triggerRule := occurrence .triggerEnable Primitives.AndRule.apply
private abbrev resetRule := occurrence .resetInverter Primitives.NotRule.apply
private abbrev matchRule := occurrence .instructionMatch InstructionMatch.Rule.apply
private abbrev immediateRule := occurrence .immediate Immediate.Rule.apply
private abbrev summaryTrapRule :=
  occurrence .instructionSummary InstructionSummary.Rule.trap
private abbrev summaryRule :=
  occurrence .instructionSummary InstructionSummary.Rule.summaries
private abbrev resetNextRule :=
  occurrence .resetMatchNext Composition.SignalComponentRule.apply
private abbrev retainedNextRule :=
  occurrence .retainedMatchNext Composition.SignalComponentRule.apply
private abbrev ordinaryNextRule :=
  occurrence .ordinarySummaryNext Composition.SignalComponentRule.apply
private abbrev resetStorageRule :=
  occurrence .resetMatchStorage Modules.EnabledResetRegister.Rule.observe
private abbrev retainedStorageRule :=
  occurrence .retainedMatchStorage Modules.EnabledRegister.Rule.observe
private abbrev immediateStorageRule :=
  occurrence .immediateStorage Modules.EnabledRegister.Rule.observe
private abbrev ordinaryStorageRule :=
  occurrence .ordinarySummaryStorage Primitives.RegisterRule.observe
private abbrev addSubStorageRule :=
  occurrence .addSubSummaryStorage Primitives.RegisterRule.observe
private abbrev compareStorageRule :=
  occurrence .compareStorage Modules.ResetRegister.Rule.observe
private abbrev immediateSelectionRule :=
  occurrence .immediateSelection Modules.Mux.Rule.select
private abbrev addSubSelectionRule :=
  occurrence .addSubSummarySelection Modules.Mux.Rule.select
private abbrev compareSelectionRule :=
  occurrence .compareSelection Modules.Mux.Rule.select
private abbrev resetOutputsRule :=
  occurrence .resetMatchOutputs Composition.SignalComponentRule.apply
private abbrev retainedOutputsRule :=
  occurrence .retainedMatchOutputs Composition.SignalComponentRule.apply
private abbrev ordinaryOutputsRule :=
  occurrence .ordinarySummaryOutputs Composition.SignalComponentRule.apply
private abbrev falseRule := occurrence .falseValue Primitives.ConstantRule.apply

private def outputOrder : List (RuleOccurrence body childContracts) :=
  [resetStorageRule, retainedStorageRule, immediateStorageRule,
    ordinaryStorageRule, addSubStorageRule, compareStorageRule,
    resetOutputsRule, retainedOutputsRule, ordinaryOutputsRule, summaryTrapRule]

private def stateOrder : List (RuleOccurrence body childContracts) :=
  [resetStorageRule, retainedStorageRule, immediateStorageRule,
    ordinaryStorageRule, addSubStorageRule, compareStorageRule,
    resetOutputsRule, retainedOutputsRule, ordinaryOutputsRule,
    pseudoRule, triggerRule, resetRule, matchRule, immediateRule, summaryRule,
    resetNextRule, retainedNextRule, ordinaryNextRule, falseRule,
    immediateSelectionRule, addSubSelectionRule, compareSelectionRule]

private def scheduleOrders : ScheduleDerivation.RuleScheduleOrders
    body childContracts cycleContract where
  output | .outputs => outputOrder
  state := stateOrder

private def derivedRuleSchedules : ScheduleDerivation.DerivedRuleSchedules
    body childContracts cycleContract := by
  derive_rule_schedules scheduleOrders

end Silean.Examples.PicoRV.Decoder.ResolveStage
