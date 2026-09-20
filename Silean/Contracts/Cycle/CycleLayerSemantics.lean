import Silean.Contracts.Cycle.CycleLayerSchedule
import Silean.Semantics.StructuralRuleSemantics

namespace Silean.Contracts.Cycle.Certification.Layer

open Silean

/-! # Structural consequences of cycle-layer schedules

Cycle contracts contribute dependency rules, and cycle-certified children
contribute certifications of those rules. All schedule semantics are proved by
the contract-independent structural scheduler. This file retains only the
cycle-specific assembly of parent output and state schedules. -/

/-- Forget the behavioral contracts of cycle-certified children while
retaining their fine-grained structural-rule certifications. -/
def structuralChildren
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (children : ChildStructures body childContracts) :
    ModuleStructuralCertification.Layer.ChildStructures body
      (childStructuralRules body childContracts) :=
  fun child => (children child).structuralCertifiedStructure

namespace RuleSchedules

/-! Parent output schedules and the parent state schedule can overlap. The
combination below replays them into one structural schedule, omitting rules
that have already been called. Replay itself belongs to the generic structural
scheduler. -/

structure Combined (body : ModuleBody)
    (childContracts : ChildCycleContracts body) where
  schedule : Schedule body childContracts (fun _ => True) (fun _ => True) []

def Combined.final (combined : Combined body childContracts) :
    Availability body childContracts :=
  combined.schedule.finalAvailability

def Combined.empty (body : ModuleBody)
    (childContracts : ChildCycleContracts body) : Combined body childContracts :=
  ⟨.done trivial⟩

noncomputable def Combined.add
    (combined : Combined body childContracts)
    {sourceInputs : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    (next : Schedule body childContracts sourceInputs Finish [])
    (inputsAvailable : ∀ input, sourceInputs input → True) :
    Combined body childContracts := by
  let replayed :=
    ModuleStructuralCertification.Layer.Schedule.replay next inputsAvailable
      (targetInitial := combined.final) (by intros; contradiction)
  exact ⟨combined.schedule.append replayed.schedule⟩

theorem Combined.add_preserves
    (combined : Combined body childContracts)
    {sourceInputs : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    (next : Schedule body childContracts sourceInputs Finish [])
    (inputsAvailable : ∀ input, sourceInputs input → True)
    (occurrence : RuleOccurrence body childContracts)
    (member : occurrence ∈ combined.final) :
    occurrence ∈ (combined.add next inputsAvailable).final := by
  let replayed :=
    ModuleStructuralCertification.Layer.Schedule.replay next inputsAvailable
      (targetInitial := combined.final) (by intros; contradiction)
  have result := replayed.covered occurrence member
  rw [← replayed.final_eq] at result
  change occurrence ∈
    (combined.schedule.append replayed.schedule).finalAvailability
  rw [Schedule.finalAvailability_append]
  exact result

theorem Combined.add_includes
    (combined : Combined body childContracts)
    {sourceInputs : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    (next : Schedule body childContracts sourceInputs Finish [])
    (inputsAvailable : ∀ input, sourceInputs input → True)
    (occurrence : RuleOccurrence body childContracts)
    (member : occurrence ∈ next.finalAvailability) :
    occurrence ∈ (combined.add next inputsAvailable).final := by
  let replayed :=
    ModuleStructuralCertification.Layer.Schedule.replay next inputsAvailable
      (targetInitial := combined.final) (by intros; contradiction)
  have result := replayed.sourceCovered occurrence member
  rw [← replayed.final_eq] at result
  change occurrence ∈
    (combined.schedule.append replayed.schedule).finalAvailability
  rw [Schedule.finalAvailability_append]
  exact result

noncomputable def combineOutputList
    (schedules : RuleSchedules body childContracts contract) :
    List contract.RuleName → Combined body childContracts
  | [] => Combined.empty body childContracts
  | name :: rest =>
      (combineOutputList schedules rest).add (schedules.output name)
        (by intro input available; trivial)

noncomputable def combineOutputs
    (schedules : RuleSchedules body childContracts contract) :
    Combined body childContracts :=
  combineOutputList schedules contract.ruleNames.values

theorem mem_combineOutputList
    (schedules : RuleSchedules body childContracts contract)
    (name : contract.RuleName) (nameMem : name ∈ names)
    (occurrence : RuleOccurrence body childContracts)
    (occurrenceMem : occurrence ∈ (schedules.output name).finalAvailability) :
    occurrence ∈ (combineOutputList schedules names).final := by
  induction names with
  | nil => cases nameMem
  | cons head tail induction =>
      rcases List.mem_cons.mp nameMem with equal | member
      · subst head
        exact Combined.add_includes _ _ _ occurrence occurrenceMem
      · exact Combined.add_preserves _ _ _ occurrence
          (induction member)

theorem mem_combineOutputs
    (schedules : RuleSchedules body childContracts contract)
    (name : contract.RuleName)
    (occurrence : RuleOccurrence body childContracts)
    (member : occurrence ∈ (schedules.output name).finalAvailability) :
    occurrence ∈ schedules.combineOutputs.final := by
  apply mem_combineOutputList schedules name
  · exact ListIndex.get_eq (contract.ruleNames.locate name) ▸ List.get_mem _ _
  · exact member

noncomputable def combined
    (schedules : RuleSchedules body childContracts contract) :
    Combined body childContracts :=
  schedules.combineOutputs |>.add schedules.state
    (by intro input available; trivial)

theorem combinedCovers
    (schedules : RuleSchedules body childContracts contract)
    (covers : schedules.CoversChildren) :
    CoversAllRules body childContracts schedules.combined.final := by
  intro child rule
  rcases covers child rule with stateMember | ⟨parentRule, outputMember⟩
  · exact Combined.add_includes schedules.combineOutputs schedules.state
      (by intro input _; trivial) _ stateMember
  · exact Combined.add_preserves schedules.combineOutputs schedules.state
      (by intro input _; trivial) _
      (mem_combineOutputs schedules parentRule _ outputMember)

theorem hasAtMostOneSolution
    (schedules : RuleSchedules body childContracts contract)
    (covers : schedules.CoversChildren)
    (children : ChildStructures body childContracts) :
    (moduleStructure body children).HasAtMostOneSolution :=
  ModuleStructuralCertification.Layer.Schedule.hasAtMostOneSolution
    schedules.combined.schedule (structuralChildren children)
    (fun _ => trivial) (schedules.combinedCovers covers)

end RuleSchedules

end Silean.Contracts.Cycle.Certification.Layer
