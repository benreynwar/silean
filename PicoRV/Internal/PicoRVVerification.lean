import PicoRV.PicoRV
import PicoRV.ControlTheorems
import PicoRV.DatapathTheorems
import PicoRV.DecoderTheorems
import PicoRV.MemoryTheorems
import PicoRV.RegsTheorems
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleRuleSchedules

/-! Internal child certifications and structural solution schedule for the
complete PicoRV hierarchy. Downstream proofs should import
`PicoRVTheorems.lean`. -/

namespace PicoRV.PicoRV.Internal

open Silean Silean.Contracts.Cycle.Certification
open Silean.Authoring

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
    Silean.Contracts.Cycle.Certification.Layer.Schedule body childContracts
      (fun _ => True)
      (Silean.Contracts.Cycle.Certification.Layer.CoversAllRules
        body childContracts) [] :=
  derivedCompleteSchedule.schedule.replaceFinish
    derivedCompleteSchedule.coversAllRules

noncomputable def stateSchedule :
    Silean.Contracts.Cycle.Certification.Layer.StateSchedule body childContracts :=
  derivedCompleteSchedule.schedule

private abbrev ParentOutputSchedule (output : Output) :=
  Silean.Contracts.Cycle.Certification.Layer.Schedule body childContracts
    (fun _ => True)
    (fun available =>
      Silean.Contracts.Cycle.Certification.Layer.sourceAvailable
        (fun _ => True) available (body.wiring.moduleOutput output)) []

noncomputable def outputSchedule (output : Output) : ParentOutputSchedule output :=
  allRulesSchedule.mapFinish fun _available covers =>
    Silean.Contracts.Cycle.Certification.Layer.sourceAvailable_of_covers
      covers (body.wiring.moduleOutput output)

theorem hasAtMostOneSolution : moduleStructure.HasAtMostOneSolution := by
  unfold moduleStructure
  have childrenEqual :
      (fun child => (certifiedChildren child).moduleStructure) =
        structuralChildren := by
    funext child
    exact certifiedChildren_moduleStructure child
  rw [← childrenEqual]
  exact allRulesSchedule.hasAtMostOneSolution certifiedChildren
    (fun _ => trivial) allRulesSchedule.finished

theorem hasSolution : moduleStructure.HasSolution := by
  unfold moduleStructure
  have childrenEqual :
      (fun child => (certifiedChildren child).moduleStructure) =
        structuralChildren := by
    funext child
    exact certifiedChildren_moduleStructure child
  rw [← childrenEqual]
  exact allRulesSchedule.hasSolution certifiedChildren allRulesSchedule.finished

end PicoRV.PicoRV.Internal
