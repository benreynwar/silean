import Silean.Examples.PicoRV.PicoRV
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation

namespace Silean.Examples.PicoRV.PicoRV

open Silean Silean.Contracts.Cycle.Certification

/-! The schedule witnesses below establish a topological order for the
blackbox contracts. They are proof inputs, not execution order stored in the
module structure. -/

private abbrev controlOutputs : Layer.RuleOccurrence body childContracts := ⟨.control, .outputs⟩
private abbrev decoderOutputs : Layer.RuleOccurrence body childContracts := ⟨.decoder, .outputs⟩
private abbrev datapathRegistered : Layer.RuleOccurrence body childContracts := ⟨.datapath, .registered⟩
private abbrev memoryRegistered : Layer.RuleOccurrence body childContracts := ⟨.mem, .registered⟩
private abbrev memoryRdataQ : Layer.RuleOccurrence body childContracts := ⟨.mem, .memRdataQ⟩
private abbrev regsRs1 : Layer.RuleOccurrence body childContracts := ⟨.cpuregs, .cpuregs_rs1⟩
private abbrev regsRs2 : Layer.RuleOccurrence body childContracts := ⟨.cpuregs, .cpuregs_rs2⟩
private abbrev datapathNextPc : Layer.RuleOccurrence body childContracts := ⟨.datapath, .nextPc⟩
private abbrev datapathComparison : Layer.RuleOccurrence body childContracts := ⟨.datapath, .comparison⟩
private abbrev datapathWriteback : Layer.RuleOccurrence body childContracts := ⟨.datapath, .writeback⟩
private abbrev memoryLaRead : Layer.RuleOccurrence body childContracts := ⟨.mem, .memLaRead⟩
private abbrev memoryLaWrite : Layer.RuleOccurrence body childContracts := ⟨.mem, .memLaWrite⟩
private abbrev memoryLaAddr : Layer.RuleOccurrence body childContracts := ⟨.mem, .memLaAddr⟩
private abbrev memoryLaWdata : Layer.RuleOccurrence body childContracts := ⟨.mem, .memLaWdata⟩
private abbrev memoryLaWstrb : Layer.RuleOccurrence body childContracts := ⟨.mem, .memLaWstrb⟩
private abbrev memoryDone : Layer.RuleOccurrence body childContracts := ⟨.mem, .memDone⟩
private abbrev memoryRdataWord : Layer.RuleOccurrence body childContracts := ⟨.mem, .memRdataWord⟩
private abbrev memoryRdataLatched : Layer.RuleOccurrence body childContracts := ⟨.mem, .memRdataLatched⟩

/-! Invoke every child rule in dependency order. From this one explicit order,
the generic derivation tactic proves both state readiness and complete coverage. -/
private def scheduleOrder : List (Layer.RuleOccurrence body childContracts) :=
  [controlOutputs, decoderOutputs, datapathRegistered, memoryRegistered,
    memoryRdataQ, regsRs1, regsRs2, datapathNextPc, datapathComparison,
    datapathWriteback, memoryLaRead, memoryLaWrite, memoryLaAddr, memoryLaWdata,
    memoryLaWstrb, memoryDone, memoryRdataWord, memoryRdataLatched]

private noncomputable def derivedCompleteSchedule :
    Layer.ScheduleDerivation.DerivedCompleteSchedule body childContracts := by
  derive_complete_schedule scheduleOrder

noncomputable def allRulesSchedule :
    Layer.Schedule body childContracts (fun _ => True) (Layer.CoversAllRules body childContracts) [] :=
  derivedCompleteSchedule.schedule.replaceFinish
    derivedCompleteSchedule.coversAllRules

noncomputable def stateSchedule : Layer.StateSchedule body childContracts :=
  derivedCompleteSchedule.schedule

abbrev ParentOutputSchedule (output : Output) :=
  Layer.Schedule body childContracts (fun _ => True)
    (fun available => Layer.sourceAvailable (fun _ => True) available
      (body.wiring.moduleOutput output)) []

noncomputable def outputSchedule (output : Output) : ParentOutputSchedule output :=
  allRulesSchedule.mapFinish fun _available covers =>
    Layer.sourceAvailable_of_covers covers (body.wiring.moduleOutput output)

theorem hasAtMostOneSolution : moduleStructure.HasAtMostOneSolution := by
  unfold moduleStructure
  exact allRulesSchedule.hasAtMostOneSolution children
    (fun _ => trivial) allRulesSchedule.finished

end Silean.Examples.PicoRV.PicoRV
