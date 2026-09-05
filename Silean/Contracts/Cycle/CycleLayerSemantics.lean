import Silean.Contracts.Cycle.CycleLayerSchedule

namespace Silean.Contracts.Cycle.Certification.Layer

open Silean

/-! Semantic consequences of the structure-first schedule vocabulary. These
proofs consume concrete children only through certifications against the
contracts already named by the layer. -/

def ChildOutputsAgree {body : ModuleBody} {childContracts : ChildCycleContracts body} {children : ChildStructures body childContracts}
    (available : Availability body childContracts)
    (left right : (name : body.context.instancePorts.Name) →
      ProposedValues (children name).moduleStructure) : Prop :=
  ∀ occurrence, occurrence ∈ available →
    ∀ output, output ∈ occurrence.writes →
      (left occurrence.child).outputs output =
        (right occurrence.child).outputs output

theorem sourceValue_eq_of_available
    {body : ModuleBody} {childContracts : ChildCycleContracts body} {children : ChildStructures body childContracts}
    {available : Availability body childContracts}
    {left right : (name : body.context.instancePorts.Name) →
      ProposedValues (children name).moduleStructure}
    (agree : ChildOutputsAgree available left right)
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (leftInputs rightInputs : body.context.ports.inputs.Values)
    (inputsAgree : ∀ input, inputAvailable input →
      leftInputs input = rightInputs input)
    (source : SignalSource body.context.ports body.context.instancePorts signalType)
    (availableSource : sourceAvailable inputAvailable available source) :
    source.value leftInputs (fun name => (left name).outputs) =
      source.value rightInputs (fun name => (right name).outputs) := by
  cases source with
  | moduleInput input => exact inputsAgree input availableSource
  | instanceOutput child output =>
      rcases availableSource with ⟨rule, member, outputMem⟩
      exact agree ⟨child, rule⟩ member output outputMem

namespace Schedule

theorem finishAgreement
    {body : ModuleBody} {childContracts : ChildCycleContracts body} {children : ChildStructures body childContracts}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable Finish initial)
    (leftInputs rightInputs : body.context.ports.inputs.Values)
    (rootInputsAgree : ∀ input, inputAvailable input →
      leftInputs input = rightInputs input)
    (currentState : (moduleStructure body children).State)
    (left right : (name : body.context.instancePorts.Name) →
      ProposedValues (children name).moduleStructure)
    (leftSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
        leftInputs left name)
      (currentState name) (left name))
    (rightSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
        rightInputs right name)
      (currentState name) (right name))
    (initialAgreement : ChildOutputsAgree initial left right) :
    ChildOutputsAgree schedule.finalAvailability left right := by
  induction schedule with
  | done finished => exact initialAgreement
  | @call available occurrence readsAvailable fresh rest induction =>
      have childInputsAgree : InputsAgreeOn occurrence.reads
          (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
            leftInputs left occurrence.child)
          (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
            rightInputs right occurrence.child) := by
        intro input inputMem
        exact sourceValue_eq_of_available initialAgreement inputAvailable
          leftInputs rightInputs rootInputsAgree
          (body.wiring.instanceInput occurrence.child input)
          (readsAvailable input inputMem)
      have writesAgree : ∀ output, output ∈ occurrence.writes →
          (left occurrence.child).outputs output =
            (right occurrence.child).outputs output := by
        exact (children occurrence.child).bundle.structuralRule occurrence.rule
          |>.determines _ _ _ _ _
            (leftSatisfies occurrence.child)
            (rightSatisfies occurrence.child)
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
    (inputAvailable : body.context.ports.inputs.Label → Prop)
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
    {sourceInputs targetInputs : body.context.ports.inputs.Label → Prop}
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

namespace StateSchedule

/-- A completed state schedule makes the inputs selected by every immediate
child state rule independent of the particular structural solution.  This is
the semantic reason for the state schedule's finish condition: scheduled
output rules determine every internal source needed by the next-state rules. -/
theorem childStateInputs_eq
    {body : ModuleBody} {childContracts : ChildCycleContracts body} {children : ChildStructures body childContracts}
    (schedule : StateSchedule body childContracts)
    (inputs : body.context.ports.inputs.Values)
    (currentState : (moduleStructure body children).State)
    (left right : (name : body.context.instancePorts.Name) →
      ProposedValues (children name).moduleStructure)
    (leftSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
        inputs left name)
      (currentState name) (left name))
    (rightSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
        inputs right name)
      (currentState name) (right name))
    (child : body.context.instancePorts.Name) :
    let selection := (childContracts child).stateRule.readsInputs
    selection.project
        (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
          inputs left child) =
      selection.project
        (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
          inputs right child) := by
  dsimp
  apply SignalGroup.project_eq_of_eq_on
  intro input inputMem
  apply sourceValue_eq_of_available
    (Schedule.finishAgreement schedule inputs inputs (fun _ _ => rfl) currentState
      left right leftSatisfies rightSatisfies (by
        intro occurrence member
        contradiction))
    (fun _ => True) inputs inputs (fun _ _ => rfl)
    (body.wiring.instanceInput child input)
  exact Schedule.finished schedule child input inputMem

/-- Consequently, a child's public next-state rule produces the same value in
any two structural solutions with the same parent inputs and current state. -/
theorem childStateRuleApply_eq
    {body : ModuleBody} {childContracts : ChildCycleContracts body} {children : ChildStructures body childContracts}
    (schedule : StateSchedule body childContracts)
    (inputs : body.context.ports.inputs.Values)
    (currentState : (moduleStructure body children).State)
    (left right : (name : body.context.instancePorts.Name) →
      ProposedValues (children name).moduleStructure)
    (leftSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
        inputs left name)
      (currentState name) (left name))
    (rightSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
        inputs right name)
      (currentState name) (right name))
    (child : body.context.instancePorts.Name)
    (contractState : (childContracts child).state.Values) :
    (childContracts child).stateRule.apply
        (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
          inputs left child)
        contractState =
      (childContracts child).stateRule.apply
        (ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
          inputs right child)
        contractState := by
  unfold CycleStateRule.apply
  rw [schedule.childStateInputs_eq inputs currentState left right
    leftSatisfies rightSatisfies child]

end StateSchedule

/-! A complete child-rule schedule is sufficient to prove uniqueness of a
composite's simultaneous structural equations. This theorem does not require a
parent behavioral contract; contracts are needed only when certifying what the
parent means, not when checking that its wiring is acyclic. -/
theorem Schedule.hasAtMostOneSolution
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    (schedule : Schedule body childContracts inputAvailable Finish [])
    (children : ChildStructures body childContracts)
    (allInputsAvailable : ∀ input, inputAvailable input)
    (covers : CoversAllRules body childContracts schedule.finalAvailability) :
    (moduleStructure body children).HasAtMostOneSolution := by
  intro inputs currentState left right leftSatisfies rightSatisfies
  rcases left with ⟨leftOutputs, leftChildren⟩
  rcases right with ⟨rightOutputs, rightChildren⟩
  change ProposedValues.boundaryOutputsSatisfy body ((fun name => (children name).moduleStructure))
      inputs leftOutputs leftChildren ∧ _ at leftSatisfies
  change ProposedValues.boundaryOutputsSatisfy body ((fun name => (children name).moduleStructure))
      inputs rightOutputs rightChildren ∧ _ at rightSatisfies
  have childOutputsAgree := Schedule.finishAgreement schedule
    inputs inputs (fun _ _ => rfl) currentState leftChildren rightChildren
    leftSatisfies.2 rightSatisfies.2
    (by intro occurrence member; cases member)
  have childInputsEqual : ∀ name,
      ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
          inputs leftChildren name =
        ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
          inputs rightChildren name := by
    intro name
    funext input
    exact sourceValue_eq_of_available childOutputsAgree inputAvailable
      inputs inputs (fun _ _ => rfl) (body.wiring.instanceInput name input)
      (sourceAvailable_mono (fun input _ => allInputsAvailable input) (fun _ member => member)
        (sourceAvailable_of_covers covers _))
  have childrenEqual : leftChildren = rightChildren := by
    funext name
    apply (children name).certification.structuralResultUnique
    · exact leftSatisfies.2 name
    · rw [childInputsEqual name]
      exact rightSatisfies.2 name
  have outputsEqual : leftOutputs = rightOutputs := by
    funext output
    rw [leftSatisfies.1 output, rightSatisfies.1 output]
    exact sourceValue_eq_of_available childOutputsAgree inputAvailable
      inputs inputs (fun _ _ => rfl) (body.wiring.moduleOutput output)
      (sourceAvailable_mono (fun input _ => allInputsAvailable input) (fun _ member => member)
        (sourceAvailable_of_covers covers _))
  cases outputsEqual
  cases childrenEqual
  rfl

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
    {sourceInputs : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    (next : Schedule body childContracts sourceInputs Finish [])
    (inputsAvailable : ∀ input, sourceInputs input → True) :
    Combined body childContracts := by
  let replayed := next.replay inputsAvailable
    (targetInitial := combined.final) (by intros; contradiction)
  exact ⟨combined.schedule.append replayed.schedule⟩

theorem Combined.add_preserves
    (combined : Combined body childContracts)
    {sourceInputs : body.context.ports.inputs.Label → Prop}
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
    {sourceInputs : body.context.ports.inputs.Label → Prop}
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
  intro inputs currentState left right leftSatisfies rightSatisfies
  rcases left with ⟨leftOutputs, leftChildren⟩
  rcases right with ⟨rightOutputs, rightChildren⟩
  change ProposedValues.boundaryOutputsSatisfy body ((fun name => (children name).moduleStructure))
      inputs leftOutputs leftChildren ∧ _ at leftSatisfies
  change ProposedValues.boundaryOutputsSatisfy body ((fun name => (children name).moduleStructure))
      inputs rightOutputs rightChildren ∧ _ at rightSatisfies
  have childOutputsAgree := Schedule.finishAgreement schedules.combined.schedule
    inputs inputs (fun _ _ => rfl) currentState leftChildren rightChildren
    leftSatisfies.2 rightSatisfies.2
    (by intro occurrence member; cases member)
  have childInputsEqual : ∀ name,
      ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
          inputs leftChildren name =
        ProposedValues.childInputs body ((fun name => (children name).moduleStructure))
          inputs rightChildren name := by
    intro name
    funext input
    exact sourceValue_eq_of_available childOutputsAgree (fun _ => True)
      inputs inputs (fun _ _ => rfl) (body.wiring.instanceInput name input)
      (sourceAvailable_of_covers combinedCovers _)
  have childrenEqual : leftChildren = rightChildren := by
    funext name
    apply (children name).certification.structuralResultUnique
    · exact leftSatisfies.2 name
    · rw [childInputsEqual name]
      exact rightSatisfies.2 name
  have outputsEqual : leftOutputs = rightOutputs := by
    funext output
    rw [leftSatisfies.1 output, rightSatisfies.1 output]
    exact sourceValue_eq_of_available childOutputsAgree (fun _ => True)
      inputs inputs (fun _ _ => rfl) (body.wiring.moduleOutput output)
      (sourceAvailable_of_covers combinedCovers _)
  cases outputsEqual
  cases childrenEqual
  rfl

end RuleSchedules

end Silean.Contracts.Cycle.Certification.Layer
