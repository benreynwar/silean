import Silean.Examples.PicoRV.PicoRV
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleRuleSchedules

namespace Silean.Examples.PicoRV.PicoRV

open Silean Silean.Contracts.Cycle.Certification
open Silean.Authoring

/-! The schedule witnesses below establish a topological order for the child
contracts. They are proof inputs, not execution order stored in the module
structure. -/

module_child_certifications childContracts for body where
  control := Control.certification,
  datapath := Datapath.certification,
  mem := Memory.certification,
  decoder := Decoder.certification,
  cpuregs := Regs.certification

/-! Invoke every child rule in dependency order. The generic declaration
checks both state readiness and complete child-rule coverage. -/
module_complete_schedule derivedCompleteSchedule for body with childContracts :=
  [.control => Control.Rule.outputs,
    .decoder => Decoder.Rule.outputs,
    .datapath => Datapath.Rule.registered,
    .mem => Memory.Rule.registered,
    .mem => Memory.Rule.memRdataQ,
    .cpuregs => Regs.Rule.cpuregs_rs1,
    .cpuregs => Regs.Rule.cpuregs_rs2,
    .datapath => Datapath.Rule.nextPc,
    .datapath => Datapath.Rule.comparison,
    .datapath => Datapath.Rule.writeback,
    .mem => Memory.Rule.memLaRead,
    .mem => Memory.Rule.memLaWrite,
    .mem => Memory.Rule.memLaAddr,
    .mem => Memory.Rule.memLaWdata,
    .mem => Memory.Rule.memLaWstrb,
    .mem => Memory.Rule.memDone,
    .mem => Memory.Rule.memRdataWord,
    .mem => Memory.Rule.memRdataLatched]

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
  have childrenEqual :
      (fun child => (certifiedChildren child).moduleStructure) = structuralChildren := by
    funext child
    exact certifiedChildren_moduleStructure child
  rw [← childrenEqual]
  exact allRulesSchedule.hasAtMostOneSolution certifiedChildren
    (fun _ => trivial) allRulesSchedule.finished

theorem hasSolution : moduleStructure.HasSolution := by
  unfold moduleStructure
  have childrenEqual :
      (fun child => (certifiedChildren child).moduleStructure) = structuralChildren := by
    funext child
    exact certifiedChildren_moduleStructure child
  rw [← childrenEqual]
  exact allRulesSchedule.hasSolution certifiedChildren allRulesSchedule.finished

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨hasSolution, hasAtMostOneSolution⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.PicoRV
