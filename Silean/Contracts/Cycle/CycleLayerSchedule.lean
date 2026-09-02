import Silean.Contracts.Cycle.CycleImplementation

namespace Silean.Contracts.Cycle.Certification.Layer

open Silean

/-! # Schedules for an uninstantiated structural layer

These are the primary schedule types. They mention only a `ModuleBody` and the
contracts required at its child boundaries; they neither select child
structures nor contain child certifications. Semantic theorems accept matching
certified children separately. -/

structure RuleOccurrence (body : ModuleBody)
    (childContracts : ChildCycleContracts body) where
  child : body.context.instancePorts.Name
  rule : (childContracts child).RuleName

namespace RuleOccurrence

@[reducible] instance : DecidableEq (RuleOccurrence body childContracts) := by
  intro left right
  rcases left with ⟨leftChild, leftRule⟩
  rcases right with ⟨rightChild, rightRule⟩
  letI : DecidableEq body.context.instancePorts.Name :=
    body.context.instancePorts.names.decidableEq
  if childEqual : leftChild = rightChild then
    subst rightChild
    letI : DecidableEq (childContracts leftChild).RuleName :=
      (childContracts leftChild).ruleNames.decidableEq
    if ruleEqual : leftRule = rightRule then
      subst rightRule
      exact isTrue rfl
    else
      exact isFalse fun equal => ruleEqual (by injection equal)
  else
    exact isFalse fun equal => childEqual (by injection equal)

def writes (occurrence : RuleOccurrence body childContracts) :
    List (body.context.instancePorts.ports occurrence.child).outputs.Label :=
  ((childContracts occurrence.child).outputRule occurrence.rule).2.writesOutputs.labels

def reads (occurrence : RuleOccurrence body childContracts) :
    List (body.context.instancePorts.ports occurrence.child).inputs.Label :=
  ((childContracts occurrence.child).outputRule occurrence.rule).2.readsInputs.labels

end RuleOccurrence

abbrev Availability (body : ModuleBody) (childContracts : ChildCycleContracts body) :=
  List (RuleOccurrence body childContracts)

/-- Every public output rule of every child has been called. -/
def CoversAllRules (body : ModuleBody) (childContracts : ChildCycleContracts body)
    (available : Availability body childContracts) : Prop :=
  ∀ child rule, RuleOccurrence.mk child rule ∈ available

def outputAvailable
    (available : Availability body childContracts)
    (child : body.context.instancePorts.Name)
    (output : (body.context.instancePorts.ports child).outputs.Label) : Prop :=
  ∃ rule, RuleOccurrence.mk child rule ∈ available ∧
    output ∈ (RuleOccurrence.mk child rule : RuleOccurrence body childContracts).writes

def sourceAvailable
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (available : Availability body childContracts)
    (source : SignalSource body.context.ports body.context.instancePorts signalType) : Prop :=
  match source with
  | .moduleInput input => inputAvailable input
  | .instanceOutput child output => outputAvailable available child output

@[simp] theorem sourceAvailable_moduleInput
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (available : Availability body childContracts)
    (input : body.context.ports.inputs.Label) :
    sourceAvailable inputAvailable available (.moduleInput input) =
      inputAvailable input := rfl

@[simp] theorem sourceAvailable_instanceOutput
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (available : Availability body childContracts)
    (child : body.context.instancePorts.Name)
    (output : (body.context.instancePorts.ports child).outputs.Label) :
    sourceAvailable inputAvailable available (.instanceOutput child output) =
      outputAvailable available child output := rfl

/-- Witness that an output is available by naming a previously called rule
that writes it. -/
theorem sourceAvailable_of_instanceOutput
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {available : Availability body childContracts}
    {child : body.context.instancePorts.Name}
    {rule : (childContracts child).RuleName}
    {output : (body.context.instancePorts.ports child).outputs.Label}
    (called : RuleOccurrence.mk child rule ∈ available)
    (written : output ∈
      (RuleOccurrence.mk child rule : RuleOccurrence body childContracts).writes) :
    sourceAvailable inputAvailable available (.instanceOutput child output) :=
  ⟨rule, called, written⟩

theorem outputAvailable_of_covers
    {available : Availability body childContracts}
    (covers : CoversAllRules body childContracts available)
    (child : body.context.instancePorts.Name)
    (output : (body.context.instancePorts.ports child).outputs.Label) :
    outputAvailable available child output := by
  have written := (childContracts child).output_is_written output
  rw [ModuleCycleContract.writtenOutputs] at written
  rcases List.mem_flatMap.mp written with ⟨rule, _, outputMem⟩
  exact ⟨rule, covers child rule, outputMem⟩

theorem sourceAvailable_of_covers
    {available : Availability body childContracts}
    (covers : CoversAllRules body childContracts available)
    (source : SignalSource body.context.ports body.context.instancePorts signalType) :
    sourceAvailable (fun _ => True) available source := by
  cases source with
  | moduleInput _ => trivial
  | instanceOutput child output => exact outputAvailable_of_covers covers child output

theorem sourceAvailable_mono
    {leftInputs rightInputs : body.context.ports.inputs.Label → Prop}
    {left right : Availability body childContracts}
    (inputsMono : ∀ input, leftInputs input → rightInputs input)
    (availableMono : ∀ occurrence, occurrence ∈ left → occurrence ∈ right)
    {source : SignalSource body.context.ports body.context.instancePorts signalType}
    (available : sourceAvailable leftInputs left source) :
    sourceAvailable rightInputs right source := by
  cases source with
  | moduleInput input => exact inputsMono input available
  | instanceOutput child output =>
      rcases available with ⟨rule, called, written⟩
      exact ⟨rule, availableMono _ called, written⟩

inductive Schedule (body : ModuleBody) (childContracts : ChildCycleContracts body)
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (Finish : Availability body childContracts → Prop) :
    Availability body childContracts → Type 1
  | done {available} (finished : Finish available) :
      Schedule body childContracts inputAvailable Finish available
  | call {available}
      (occurrence : RuleOccurrence body childContracts)
      (readsAvailable : ∀ input, input ∈ occurrence.reads →
        sourceAvailable inputAvailable available
          (body.wiring.instanceInput occurrence.child input))
      (fresh : occurrence ∉ available)
      (rest : Schedule body childContracts inputAvailable Finish
        (occurrence :: available)) :
      Schedule body childContracts inputAvailable Finish available

namespace Schedule

def finalAvailability
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts} :
    Schedule body childContracts inputAvailable Finish initial →
      Availability body childContracts
  | .done (available := available) _ => available
  | .call _ _ _ rest => rest.finalAvailability

@[simp] theorem finalAvailability_done
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {available : Availability body childContracts}
    (finished : Finish available) :
    finalAvailability (.done finished :
      Schedule body childContracts inputAvailable Finish available) = available := rfl

@[simp] theorem finalAvailability_call
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {available : Availability body childContracts}
    (occurrence : RuleOccurrence body childContracts)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (fresh : occurrence ∉ available)
    (rest : Schedule body childContracts inputAvailable Finish
      (occurrence :: available)) :
    finalAvailability (.call occurrence readsAvailable fresh rest) =
      finalAvailability rest := rfl

noncomputable def append
    {body : ModuleBody} {children : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body children → Prop}
    {initial : Availability body children}
    (first : Schedule body children inputAvailable FirstFinish initial)
    (second : Schedule body children inputAvailable SecondFinish
      first.finalAvailability) :
    Schedule body children inputAvailable SecondFinish initial := by
  induction first with
  | done _ => exact second
  | call occurrence readsAvailable fresh rest induction =>
      exact .call occurrence readsAvailable fresh (induction second)

@[simp] theorem finalAvailability_append
    {body : ModuleBody} {children : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body children → Prop}
    {initial : Availability body children}
    (first : Schedule body children inputAvailable FirstFinish initial)
    (second : Schedule body children inputAvailable SecondFinish
      first.finalAvailability) :
    (first.append second).finalAvailability = second.finalAvailability := by
  induction first with
  | done _ => rfl
  | call occurrence readsAvailable fresh rest induction =>
      exact induction second

/-! Call one rule for every member of a finite family. All reads must already
be available before the family starts, so enumeration order is semantically
irrelevant. -/

private noncomputable def callFamilyFrom
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Index : Type} (occurrence : Index → RuleOccurrence body childContracts)
    (injective : Function.Injective occurrence)
    (initial : Availability body childContracts)
    (initialReads : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable initial
        (body.wiring.instanceInput (occurrence index).child input))
    (remaining : List Index) (remainingNodup : remaining.Nodup)
    (available : Availability body childContracts)
    (initialIncluded : ∀ called, called ∈ initial → called ∈ available)
    (fresh : ∀ index, index ∈ remaining → occurrence index ∉ available)
    (Finish : Availability body childContracts → Prop)
    (finish : ∀ final,
      (∀ called, called ∈ available → called ∈ final) →
      (∀ index, index ∈ remaining → occurrence index ∈ final) →
      (∀ called, called ∈ final →
        called ∈ available ∨ ∃ index, index ∈ remaining ∧ called = occurrence index) →
      Finish final) :
    Schedule body childContracts inputAvailable Finish available :=
  match remaining with
  | [] => .done (finish available (fun _ member => member)
      (fun _ member => nomatch member) (fun _ member => Or.inl member))
  | index :: rest => by
      have indexFresh : index ∉ rest := (List.nodup_cons.mp remainingNodup).1
      let called := occurrence index
      refine .call called ?_ (fresh index (by simp)) ?_
      · intro input inputMem
        exact sourceAvailable_mono (fun _ available => available)
          initialIncluded (initialReads index input inputMem)
      · apply callFamilyFrom occurrence injective initial initialReads rest
          (List.nodup_cons.mp remainingNodup).2 (called :: available)
        · intro previous member
          exact List.mem_cons_of_mem called (initialIncluded previous member)
        · intro next nextMem member
          rcases List.mem_cons.mp member with equal | oldMember
          · apply indexFresh
            rw [← injective equal]
            exact nextMem
          · exact fresh next (List.mem_cons_of_mem index nextMem) oldMember
        · intro final includes covers only
          apply finish final
          · intro previous member
            exact includes previous (List.mem_cons_of_mem called member)
          · intro selected selectedMem
            rcases List.mem_cons.mp selectedMem with equal | tailMem
            · subst selected
              exact includes called (by simp)
            · exact covers selected tailMem
          · intro selected selectedMem
            rcases only selected selectedMem with inExtended | fromTail
            · rcases List.mem_cons.mp inExtended with equal | inAvailable
              · exact Or.inr ⟨index, by simp, equal⟩
              · exact Or.inl inAvailable
            · rcases fromTail with ⟨next, nextMem, equal⟩
              exact Or.inr ⟨next, List.mem_cons_of_mem index nextMem, equal⟩
termination_by remaining.length

noncomputable def callFamilyAfter
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    (initial : Availability body childContracts)
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence body childContracts)
    (injective : Function.Injective occurrence)
    (fresh : ∀ index, occurrence index ∉ initial)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable initial
        (body.wiring.instanceInput (occurrence index).child input)) :
    Schedule body childContracts inputAvailable
      (fun final =>
        (∀ called, called ∈ initial → called ∈ final) ∧
        (∀ index, occurrence index ∈ final) ∧
        ∀ called, called ∈ final →
          called ∈ initial ∨ ∃ index, called = occurrence index) initial :=
  callFamilyFrom occurrence injective initial readsAvailable indices.values
    indices.nodup initial (fun _ member => member)
    (fun index _ => fresh index) _
    (fun _ includes covers only => ⟨includes, ⟨
      (fun index => covers index
        (ListIndex.get_eq (indices.locate index) ▸ List.get_mem _ _)),
      (fun called member => by
        rcases only called member with present | found
        · exact Or.inl present
        · rcases found with ⟨index, _, equal⟩
          exact Or.inr ⟨index, equal⟩)⟩⟩)

noncomputable def callFamily
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence body childContracts)
    (injective : Function.Injective occurrence)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable ([] : Availability body childContracts)
        (body.wiring.instanceInput (occurrence index).child input)) :
    Schedule body childContracts inputAvailable
      (fun final =>
        (∀ index, occurrence index ∈ final) ∧
        ∀ called, called ∈ final → ∃ index, called = occurrence index) [] :=
  callFamilyFrom occurrence injective [] readsAvailable indices.values indices.nodup []
    (fun _ member => nomatch member) (fun _ _ member => nomatch member) _
    (fun _ _ covers only => ⟨
      (fun index => covers index
        (ListIndex.get_eq (indices.locate index) ▸ List.get_mem _ _)),
      (fun called member => by
        rcases only called member with impossible | found
        · cases impossible
        · rcases found with ⟨index, _, equal⟩
          exact ⟨index, equal⟩)⟩)

theorem finished
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable Finish initial) :
    Finish schedule.finalAvailability := by
  induction schedule with
  | done finished => exact finished
  | call _ _ _ _ induction => exact induction

@[simp] theorem mem_finalAvailability_callFamilyAfter_iff
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    (initial : Availability body childContracts)
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence body childContracts)
    (injective : Function.Injective occurrence)
    (fresh : ∀ index, occurrence index ∉ initial)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable initial
        (body.wiring.instanceInput (occurrence index).child input))
    (called : RuleOccurrence body childContracts) :
    called ∈ (callFamilyAfter initial indices occurrence injective fresh
      readsAvailable).finalAvailability ↔
      called ∈ initial ∨ ∃ index, called = occurrence index := by
  let family := callFamilyAfter initial indices occurrence injective fresh readsAvailable
  constructor
  · exact family.finished.2.2 called
  · intro member
    rcases member with old | ⟨index, equal⟩
    · exact family.finished.1 called old
    · rw [equal]
      exact family.finished.2.1 index

/-- Change only the final obligation of a schedule. -/
noncomputable def mapFinish
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable FirstFinish initial)
    (implies : ∀ available, FirstFinish available → SecondFinish available) :
    Schedule body childContracts inputAvailable SecondFinish initial := by
  induction schedule with
  | done finished => exact .done (implies _ finished)
  | call occurrence readsAvailable fresh rest induction =>
      exact .call occurrence readsAvailable fresh induction

/-- Replace a schedule's terminal obligation with another fact proved for its
actual final availability. Unlike `mapFinish`, this does not require an
implication that holds at every intermediate availability. -/
noncomputable def replaceFinish
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable FirstFinish initial)
    (finished : SecondFinish schedule.finalAvailability) :
    Schedule body childContracts inputAvailable SecondFinish initial := by
  induction schedule with
  | done _ => exact .done finished
  | call occurrence readsAvailable fresh rest induction =>
      exact .call occurrence readsAvailable fresh (induction finished)

end Schedule

def BoundaryReady (body : ModuleBody) (childContracts : ChildCycleContracts body)
    (outputs : List body.context.ports.outputs.Label)
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (available : Availability body childContracts) : Prop :=
  ∀ output, output ∈ outputs →
    sourceAvailable inputAvailable available (body.wiring.moduleOutput output)

abbrev OutputSchedule (body : ModuleBody)
    (childContracts : ChildCycleContracts body)
    (contract : ModuleCycleContract body.context.ports)
    (name : contract.RuleName) :=
  let rule := (contract.outputRule name).2
  Schedule body childContracts
    (fun input => input ∈ rule.readsInputs.labels)
    (BoundaryReady body childContracts rule.writesOutputs.labels
      (fun input => input ∈ rule.readsInputs.labels)) []

def ChildrenStateInputsReady (body : ModuleBody)
    (childContracts : ChildCycleContracts body)
    (available : Availability body childContracts) : Prop :=
  ∀ child input,
    input ∈ (childContracts child).stateRule.readsInputs.labels →
    sourceAvailable (fun _ => True) available
      (body.wiring.instanceInput child input)

abbrev StateSchedule (body : ModuleBody)
    (childContracts : ChildCycleContracts body) :=
  Schedule body childContracts (fun _ => True)
    (ChildrenStateInputsReady body childContracts) []

structure RuleSchedules (body : ModuleBody)
    (childContracts : ChildCycleContracts body)
    (contract : ModuleCycleContract body.context.ports) where
  output : ∀ name, OutputSchedule body childContracts contract name
  state : StateSchedule body childContracts

namespace RuleSchedules

/-- Every child rule must occur in the parent state schedule or in at least one
parent output schedule. This is the implementation-independent coverage
obligation stored with a layer. -/
def CoversChildren (schedules : RuleSchedules body childContracts contract) : Prop :=
  ∀ child rule,
    RuleOccurrence.mk child rule ∈ schedules.state.finalAvailability ∨
      ∃ parentRule, RuleOccurrence.mk child rule ∈
        (schedules.output parentRule).finalAvailability

/-- When every child rule occurs in an output schedule, coverage follows
without mentioning the (irrelevant) state schedule. -/
theorem coversChildren_of_outputMembership
    (schedules : RuleSchedules body childContracts contract)
    (covered : ∀ child rule, ∃ parentRule,
      RuleOccurrence.mk child rule ∈
        (schedules.output parentRule).finalAvailability) :
    schedules.CoversChildren := by
  intro child rule
  exact Or.inr (covered child rule)

end RuleSchedules

end Silean.Contracts.Cycle.Certification.Layer
