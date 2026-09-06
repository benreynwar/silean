import Silean.Examples.PicoRV.Decoder.DecoderResolveStageStructure
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.EnabledRegister.EnabledRegisterCertified
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterCertified
import Silean.Modules.Register.Register
import Silean.Modules.ResetRegister.ResetRegisterCertified
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.Constant.Constant
import Silean.Primitives.Not

namespace Silean.Examples.PicoRV.Decoder.ResolveStage

open Silean
open Silean.Authoring
open Silean.Examples.PicoRV.Decoder

/-! ## Child contracts and structural schedules

The three combinational decoder children are deliberately certified as their
contract blackboxes here. The explicit orders are the only module-specific
scheduling information; `module_rule_schedules` checks their dependencies and
constructs the proof-bearing schedules and child-rule coverage proof. -/

module_child_certifications childContracts for body where
  pseudoInverter := Primitives.notCertified.certification,
  triggerEnable := Primitives.andCertified.certification,
  resetInverter := Primitives.notCertified.certification,
  instructionMatch := InstructionMatch.cycleContract.blackboxCertification,
  immediate := Immediate.cycleContract.blackboxCertification,
  instructionSummary := InstructionSummary.cycleContract.blackboxCertification,
  resetMatchNext := resetMatchCombiner.certified.certification,
  retainedMatchNext := retainedMatchCombiner.certified.certification,
  ordinarySummaryNext := ordinarySummaryCombiner.certified.certification,
  resetMatchStorage := Modules.EnabledResetRegister.certification
    resetMatchType falseResetMatches,
  retainedMatchStorage := Modules.EnabledRegister.certification retainedMatchType,
  immediateStorage := Modules.EnabledRegister.certification immediateType,
  ordinarySummaryStorage := Modules.Register.certification ordinarySummaryType,
  addSubSummaryStorage := Modules.Register.certification .bit,
  compareStorage := Modules.ResetRegister.certification .bit false,
  immediateSelection := Modules.Mux.certification immediateType,
  addSubSummarySelection := Modules.Mux.certification .bit,
  compareSelection := Modules.Mux.certification .bit,
  resetMatchOutputs := resetMatchSplitter.certified.certification,
  retainedMatchOutputs := retainedMatchSplitter.certified.certification,
  ordinarySummaryOutputs := ordinarySummarySplitter.certified.certification,
  falseValue := Modules.Constant.certification .bit false

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .outputs => [.resetMatchStorage => Modules.EnabledResetRegister.Rule.observe,
      .retainedMatchStorage => Modules.EnabledRegister.Rule.observe,
      .immediateStorage => Modules.EnabledRegister.Rule.observe,
      .ordinarySummaryStorage => Primitives.RegisterRule.observe,
      .addSubSummaryStorage => Primitives.RegisterRule.observe,
      .compareStorage => Modules.ResetRegister.Rule.observe,
      .resetMatchOutputs => Composition.SignalComponentRule.apply,
      .retainedMatchOutputs => Composition.SignalComponentRule.apply,
      .ordinarySummaryOutputs => Composition.SignalComponentRule.apply,
      .instructionSummary => InstructionSummary.Rule.trap]
  state := [.resetMatchStorage => Modules.EnabledResetRegister.Rule.observe,
    .retainedMatchStorage => Modules.EnabledRegister.Rule.observe,
    .immediateStorage => Modules.EnabledRegister.Rule.observe,
    .ordinarySummaryStorage => Primitives.RegisterRule.observe,
    .addSubSummaryStorage => Primitives.RegisterRule.observe,
    .compareStorage => Modules.ResetRegister.Rule.observe,
    .resetMatchOutputs => Composition.SignalComponentRule.apply,
    .retainedMatchOutputs => Composition.SignalComponentRule.apply,
    .ordinarySummaryOutputs => Composition.SignalComponentRule.apply,
    .pseudoInverter => Primitives.NotRule.apply,
    .triggerEnable => Primitives.AndRule.apply,
    .resetInverter => Primitives.NotRule.apply,
    .instructionMatch => InstructionMatch.Rule.apply,
    .immediate => Immediate.Rule.apply,
    .instructionSummary => InstructionSummary.Rule.summaries,
    .resetMatchNext => Composition.SignalComponentRule.apply,
    .retainedMatchNext => Composition.SignalComponentRule.apply,
    .ordinarySummaryNext => Composition.SignalComponentRule.apply,
    .falseValue => Primitives.ConstantRule.apply,
    .immediateSelection => Modules.Mux.Rule.select,
    .addSubSummarySelection => Modules.Mux.Rule.select,
    .compareSelection => Modules.Mux.Rule.select]

end Silean.Examples.PicoRV.Decoder.ResolveStage
