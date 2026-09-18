import Silean.Contracts.Cycle.CycleLayerSchedule

namespace Silean.Contracts.Cycle.Certification.Layer

open Silean

/-! Semantic consequences of the structure-first schedule vocabulary. These
proofs consume concrete children only through certifications against the
contracts already named by the layer. -/

def ChildOutputsAgree {body : ModuleBody}
    {childContracts : ChildCycleContracts body}
    {children : ChildStructures body childContracts}
    (available : Availability body childContracts)
    (left right : HierStep (moduleStructure body children)) : Prop :=
  ∀ occurrence, occurrence ∈ available →
    ∀ output, output ∈ occurrence.writes →
      (left.children occurrence.child).outputs output =
        (right.children occurrence.child).outputs output

theorem sourceValue_eq_of_available
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {children : ChildStructures body childContracts}
    {available : Availability body childContracts}
    {left right : HierStep (moduleStructure body children)}
    (agree : ChildOutputsAgree available left right)
    (inputAvailable : body.ports.inputs.Label → Prop)
    (leftInputs rightInputs : body.ports.inputs.Values)
    (inputsAgree : ∀ input, inputAvailable input →
      leftInputs input = rightInputs input)
    (source : SignalSource body.ports body.instancePorts signalType)
    (availableSource : sourceAvailable inputAvailable available source) :
    source.value leftInputs left.childOutputs =
      source.value rightInputs right.childOutputs := by
  cases source with
  | moduleInput input => exact inputsAgree input availableSource
  | instanceOutput child output =>
      rcases availableSource with ⟨rule, member, outputMem⟩
      exact agree ⟨child, rule⟩ member output outputMem

namespace Schedule

theorem finishAgreement
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {children : ChildStructures body childContracts}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable Finish initial)
    (left right : HierStep (moduleStructure body children))
    (rootInputsAgree : ∀ input, inputAvailable input →
      left.inputs input = right.inputs input)
    (leftSatisfies : (moduleStructure body children).IsSolution left)
    (rightSatisfies : (moduleStructure body children).IsSolution right)
    (currentStatesEqual :
      HierStep.currentState (moduleStructure body children) left =
        HierStep.currentState (moduleStructure body children) right)
    (initialAgreement : ChildOutputsAgree initial left right) :
    ChildOutputsAgree schedule.finalAvailability left right := by
  induction schedule with
  | done finished => exact initialAgreement
  | @call available occurrence readsAvailable fresh rest induction =>
      have childInputsAgree : InputsAgreeOn occurrence.reads
          (left.children occurrence.child).inputs
          (right.children occurrence.child).inputs := by
        intro input inputMem
        have sourceEqual := sourceValue_eq_of_available initialAgreement
          inputAvailable left.inputs right.inputs rootInputsAgree
          (body.wiring.instanceInput occurrence.child input)
          (readsAvailable input inputMem)
        exact congrFun (leftSatisfies.2.1 occurrence.child) input |>.trans
          (sourceEqual.trans
            (congrFun (rightSatisfies.2.1 occurrence.child).symm input))
      have writesAgree : ∀ output, output ∈ occurrence.writes →
          (left.children occurrence.child).outputs output =
            (right.children occurrence.child).outputs output := by
        exact (children occurrence.child).bundle.structuralRule occurrence.rule
          |>.determines _ _
            (leftSatisfies.2.2 occurrence.child)
            (rightSatisfies.2.2 occurrence.child)
            (congrFun currentStatesEqual occurrence.child)
            childInputsAgree
      have extended : ChildOutputsAgree (occurrence :: available) left right := by
        intro called member output outputMem
        rcases List.mem_cons.mp member with equal | member
        · cases equal
          exact writesAgree output outputMem
        · exact initialAgreement called member output outputMem
      exact induction extended

structure ReplayResult {body : ModuleBody}
    {childContracts : ChildCycleContracts body}
    (inputAvailable : body.ports.inputs.Label → Prop)
    (initial : Availability body childContracts)
    (sourceFinal : Availability body childContracts)
    (SourceFinish : Availability body childContracts → Prop) where
  final : Availability body childContracts
  schedule : Schedule body childContracts inputAvailable (fun _ => True) initial
  final_eq : schedule.finalAvailability = final
  covered : ∀ occurrence, occurrence ∈ initial → occurrence ∈ final
  sourceFinished : SourceFinish sourceFinal
  sourceCovered : ∀ occurrence, occurrence ∈ sourceFinal → occurrence ∈ final

/-! Replay one schedule after an existing call sequence. Calls already present
in the target availability are omitted. The result remembers that every
previously available occurrence remains covered. -/

noncomputable def replay {body : ModuleBody}
    {childContracts : ChildCycleContracts body}
    {sourceInputs targetInputs : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {sourceInitial targetInitial : Availability body childContracts}
    (schedule : Schedule body childContracts sourceInputs Finish sourceInitial)
    (inputsMono : ∀ input, sourceInputs input → targetInputs input)
    (initialCovered : ∀ occurrence, occurrence ∈ sourceInitial →
      occurrence ∈ targetInitial) :
    ReplayResult targetInputs targetInitial schedule.finalAvailability Finish := by
  letI : DecidableEq (RuleOccurrence body childContracts) := inferInstance
  induction schedule generalizing targetInitial with
  | done finished =>
      exact ⟨targetInitial, .done trivial, rfl,
        (by intro occurrence member; exact member),
        finished, initialCovered⟩
  | @call sourceAvailable occurrence readsAvailable fresh rest induction =>
      if already : occurrence ∈ targetInitial then
        apply induction (targetInitial := targetInitial)
        intro previous member
        rcases List.mem_cons.mp member with equal | member
        · cases equal
          exact already
        · exact initialCovered previous member
      else
        let replayed := induction (targetInitial := occurrence :: targetInitial)
          (fun previous member => by
            rcases List.mem_cons.mp member with equal | member
            · exact List.mem_cons.mpr (Or.inl equal)
            · exact List.mem_cons.mpr (Or.inr (initialCovered previous member)))
        refine ⟨replayed.final, .call occurrence ?_ already replayed.schedule,
          ?_, ?_, replayed.sourceFinished, replayed.sourceCovered⟩
        · intro input inputMem
          exact sourceAvailable_mono inputsMono initialCovered
            (readsAvailable input inputMem)
        · exact replayed.final_eq
        · intro previous member
          exact replayed.covered previous (List.mem_cons_of_mem occurrence member)

end Schedule

/-! A complete child-rule schedule is sufficient to prove uniqueness of a
composite's simultaneous structural equations. This theorem does not require a
parent behavioral contract; contracts are needed only when certifying what the
parent means, not when checking that its wiring is acyclic. -/
theorem Schedule.hasAtMostOneSolution
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    (schedule : Schedule body childContracts inputAvailable Finish [])
    (children : ChildStructures body childContracts)
    (allInputsAvailable : ∀ input, inputAvailable input)
    (covers : CoversAllRules body childContracts schedule.finalAvailability) :
    (moduleStructure body children).HasAtMostOneSolution := by
  intro left right leftSatisfies rightSatisfies inputsEqual currentStatesEqual
  have childOutputsAgree := Schedule.finishAgreement schedule
    left right (fun input _ => congrFun inputsEqual input)
    leftSatisfies rightSatisfies currentStatesEqual
    (by intro occurrence member; cases member)
  have childInputsEqual : ∀ name,
      (left.children name).inputs = (right.children name).inputs := by
    intro name
    funext input
    have sourceEqual := sourceValue_eq_of_available childOutputsAgree
      inputAvailable left.inputs right.inputs
      (fun rootInput _ => congrFun inputsEqual rootInput)
      (body.wiring.instanceInput name input)
      (sourceAvailable_mono
        (fun rootInput _ => allInputsAvailable rootInput)
        (fun _ member => member) (sourceAvailable_of_covers covers _))
    exact (congrFun (leftSatisfies.2.1 name) input).trans
      (sourceEqual.trans (congrFun (rightSatisfies.2.1 name).symm input))
  have childrenEqual : left.children = right.children := by
    funext name
    apply (children name).certification.structuralResultUnique
    · exact leftSatisfies.2.2 name
    · exact rightSatisfies.2.2 name
    · exact childInputsEqual name
    · exact congrFun currentStatesEqual name
  have outputsEqual : left.outputs = right.outputs := by
    funext output
    rw [leftSatisfies.1 output, rightSatisfies.1 output]
    exact sourceValue_eq_of_available childOutputsAgree inputAvailable
      left.inputs right.inputs
      (fun input _ => congrFun inputsEqual input)
      (body.wiring.moduleOutput output)
      (sourceAvailable_mono
        (fun input _ => allInputsAvailable input)
        (fun _ member => member) (sourceAvailable_of_covers covers _))
  exact CompositeHierStep.ext inputsEqual outputsEqual childrenEqual

namespace RuleSchedules

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
  let replayed := next.replay inputsAvailable
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
  let replayed := next.replay inputsAvailable
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
  let replayed := next.replay inputsAvailable
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

theorem hasAtMostOneSolution
    (schedules : RuleSchedules body childContracts contract)
    (covers : schedules.CoversChildren)
    (children : ChildStructures body childContracts) :
    (moduleStructure body children).HasAtMostOneSolution := by
  have combinedCovers : CoversAllRules body childContracts
      schedules.combined.final := by
    intro child rule
    rcases covers child rule with stateMember | ⟨parentRule, outputMember⟩
    · exact Combined.add_includes schedules.combineOutputs schedules.state
        (by intro input _; trivial) _ stateMember
    · exact Combined.add_preserves schedules.combineOutputs schedules.state
        (by intro input _; trivial) _
        (mem_combineOutputs schedules parentRule _ outputMember)
  exact schedules.combined.schedule.hasAtMostOneSolution children
    (fun _ => trivial) combinedCovers

end RuleSchedules

end Silean.Contracts.Cycle.Certification.Layer
