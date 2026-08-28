import Silean.Contracts.Cycle.CycleComposition

namespace Silean.Contracts.Cycle.Certification

open Silean

/-! Proof machinery for certifying composite modules. A schedule orders calls
to child contract rules so each required child input is already available. It
is a proof witness, not part of `ModuleStructure` or a certified module's public
interface. -/

structure RuleOccurrence {body : ModuleBody} (children : Children body) where
  /-- Child instance whose public contract rule is invoked. -/
  child : body.context.instancePorts.Name
  /-- Rule invoked on that child. -/
  rule : (children child).cycleContract.RuleName

namespace RuleOccurrence

def decidableEq {body : ModuleBody} {children : Children body} :
    DecidableEq (RuleOccurrence children) := by
  intro left right
  rcases left with ⟨leftChild, leftRule⟩
  rcases right with ⟨rightChild, rightRule⟩
  letI : DecidableEq body.context.instancePorts.Name :=
    body.context.instancePorts.names.decidableEq
  if childEqual : leftChild = rightChild then
    subst rightChild
    letI : DecidableEq (children leftChild).cycleContract.RuleName :=
      (children leftChild).cycleContract.ruleNames.decidableEq
    if ruleEqual : leftRule = rightRule then
      subst rightRule
      exact isTrue rfl
    else
      exact isFalse fun equal => ruleEqual (by injection equal)
  else
    exact isFalse fun equal => childEqual (by injection equal)

def writes {body : ModuleBody} {children : Children body}
    (occurrence : RuleOccurrence children) :
    List (body.context.instancePorts.ports occurrence.child).outputs.Label :=
  ((children occurrence.child).cycleContract.outputRule occurrence.rule).2.writesOutputs.labels

def reads {body : ModuleBody} {children : Children body}
    (occurrence : RuleOccurrence children) :
    List (body.context.instancePorts.ports occurrence.child).inputs.Label :=
  ((children occurrence.child).cycleContract.outputRule occurrence.rule).2.readsInputs.labels

end RuleOccurrence

abbrev Availability {body : ModuleBody} (children : Children body) :=
  List (RuleOccurrence children)

def outputAvailable {body : ModuleBody} {children : Children body}
    (available : Availability children)
    (child : body.context.instancePorts.Name)
    (output : (body.context.instancePorts.ports child).outputs.Label) : Prop :=
  ∃ rule, RuleOccurrence.mk child rule ∈ available ∧
    output ∈ (RuleOccurrence.mk child rule : RuleOccurrence children).writes

def sourceAvailable {body : ModuleBody} {children : Children body}
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (available : Availability children)
    (source : SignalSource body.context.ports body.context.instancePorts signalType) : Prop :=
  match source with
  | .moduleInput input => inputAvailable input
  | .instanceOutput child output => outputAvailable available child output

def ChildOutputsAgree {body : ModuleBody} {children : Children body}
    (available : Availability children)
    (left right : (name : body.context.instancePorts.Name) →
      ProposedValues (children name).moduleStructure) : Prop :=
  ∀ occurrence, occurrence ∈ available →
    ∀ output, output ∈ occurrence.writes →
      (left occurrence.child).outputs output =
        (right occurrence.child).outputs output

theorem source_value_eq_of_available
    {body : ModuleBody} {children : Children body}
    {available : Availability children}
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

theorem outputAvailable_mono {body : ModuleBody} {children : Children body}
    {left right : Availability children}
    (subset : ∀ occurrence, occurrence ∈ left → occurrence ∈ right)
    {child : body.context.instancePorts.Name}
    {output : (body.context.instancePorts.ports child).outputs.Label}
    (available : outputAvailable left child output) :
    outputAvailable right child output := by
  rcases available with ⟨rule, member, writes⟩
  exact ⟨rule, subset _ member, writes⟩

theorem sourceAvailable_mono {body : ModuleBody} {children : Children body}
    {leftInputs rightInputs : body.context.ports.inputs.Label → Prop}
    {left right : Availability children}
    (inputsMono : ∀ input, leftInputs input → rightInputs input)
    (outputsMono : ∀ occurrence, occurrence ∈ left → occurrence ∈ right)
    {source : SignalSource body.context.ports body.context.instancePorts signalType}
    (available : sourceAvailable leftInputs left source) :
    sourceAvailable rightInputs right source := by
  cases source with
  | moduleInput input => exact inputsMono input available
  | instanceOutput child output =>
      exact outputAvailable_mono outputsMono available

/-! A schedule calls named rules from certified child contracts. It contains no
child structural rule, evaluator, or child-local schedule. -/

inductive Schedule (body : ModuleBody) (children : Children body)
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (Finish : Availability children → Prop) :
    Availability children → Type 1
  /-- Finish once the required child outputs are available. -/
  | done {available} (finished : Finish available) :
      Schedule body children inputAvailable Finish available

  /-- Invoke one fresh child rule whose inputs are already available. -/
  | call {available}
      (occurrence : RuleOccurrence children)
      (readsAvailable : ∀ input, input ∈ occurrence.reads →
        sourceAvailable inputAvailable available
          (body.wiring.instanceInput occurrence.child input))
      (fresh : occurrence ∉ available)
      (rest : Schedule body children inputAvailable Finish
        (occurrence :: available)) :
      Schedule body children inputAvailable Finish available

namespace Schedule

def finalAvailability {body : ModuleBody} {children : Children body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability children → Prop}
    {initial : Availability children} :
    Schedule body children inputAvailable Finish initial → Availability children
  | .done (available := available) _ => available
  | .call _ _ _ rest => rest.finalAvailability

theorem finished {body : ModuleBody} {children : Children body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability children → Prop}
    {initial : Availability children}
    (schedule : Schedule body children inputAvailable Finish initial) :
    Finish schedule.finalAvailability := by
  induction schedule with
  | done finished => exact finished
  | call _ _ _ _ induction => exact induction

theorem finishAgreement
    {body : ModuleBody} {children : Children body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability children → Prop}
    {initial : Availability children}
    (schedule : Schedule body children inputAvailable Finish initial)
    (leftInputs rightInputs : body.context.ports.inputs.Values)
    (rootInputsAgree : ∀ input, inputAvailable input →
      leftInputs input = rightInputs input)
    (currentState : (moduleStructure body children).State)
    (left right : (name : body.context.instancePorts.Name) →
      ProposedValues (children name).moduleStructure)
    (leftSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body (childStructure children)
        leftInputs left name)
      (currentState name) (left name))
    (rightSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body (childStructure children)
        rightInputs right name)
      (currentState name) (right name))
    (initialAgreement : ChildOutputsAgree initial left right) :
    ChildOutputsAgree schedule.finalAvailability left right := by
  induction schedule with
  | done finished => exact initialAgreement
  | @call available occurrence readsAvailable fresh rest induction =>
      have childInputsAgree : InputsAgreeOn occurrence.reads
          (ProposedValues.childInputs body (childStructure children)
            leftInputs left occurrence.child)
          (ProposedValues.childInputs body (childStructure children)
            rightInputs right occurrence.child) := by
        intro input inputMem
        exact source_value_eq_of_available initialAgreement inputAvailable
          leftInputs rightInputs rootInputsAgree
          (body.wiring.instanceInput occurrence.child input)
          (readsAvailable input inputMem)
      have writesAgree : ∀ output, output ∈ occurrence.writes →
          (left occurrence.child).outputs output =
            (right occurrence.child).outputs output := by
        exact (children occurrence.child).structuralRule occurrence.rule
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

noncomputable def append {body : ModuleBody} {children : Children body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability children → Prop}
    {initial : Availability children}
    (first : Schedule body children inputAvailable FirstFinish initial)
    (second : Schedule body children inputAvailable SecondFinish
      first.finalAvailability) :
    Schedule body children inputAvailable SecondFinish initial := by
  induction first with
  | done finished => exact second
  | call occurrence readsAvailable fresh rest induction =>
      exact .call occurrence readsAvailable fresh (induction second)

theorem finalAvailability_append
    {body : ModuleBody} {children : Children body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability children → Prop}
    {initial : Availability children}
    (first : Schedule body children inputAvailable FirstFinish initial)
    (second : Schedule body children inputAvailable SecondFinish
      first.finalAvailability) :
    (first.append second).finalAvailability = second.finalAvailability := by
  induction first with
  | done finished => rfl
  | call occurrence readsAvailable fresh rest induction =>
      exact induction second

/-! Construct one schedule call per member of a finite family. Every call's
reads must already be available before the family starts, so the result does
not introduce an accidental dependency on enumeration order. -/

private noncomputable def callFamilyFrom
    {body : ModuleBody} {children : Children body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Index : Type} (occurrence : Index → RuleOccurrence children)
    (injective : Function.Injective occurrence)
    (initial : Availability children)
    (initialReads : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable initial
        (body.wiring.instanceInput (occurrence index).child input))
    (remaining : List Index) (remainingNodup : remaining.Nodup)
    (available : Availability children)
    (initialIncluded : ∀ called, called ∈ initial → called ∈ available)
    (fresh : ∀ index, index ∈ remaining → occurrence index ∉ available)
    (Finish : Availability children → Prop)
    (finish : ∀ final,
      (∀ called, called ∈ available → called ∈ final) →
      (∀ index, index ∈ remaining → occurrence index ∈ final) →
      (∀ called, called ∈ final →
        called ∈ available ∨ ∃ index, index ∈ remaining ∧ called = occurrence index) →
      Finish final) :
    Schedule body children inputAvailable Finish available :=
  match remaining with
  | [] => .done (finish available (fun _ member => member)
      (fun _ member => nomatch member) (fun called member => Or.inl member))
  | index :: rest => by
      have indexFresh : index ∉ rest := (List.nodup_cons.mp remainingNodup).1
      have restNodup : rest.Nodup := (List.nodup_cons.mp remainingNodup).2
      let called := occurrence index
      refine .call called ?_ (fresh index (by simp)) ?_
      · intro input inputMem
        exact sourceAvailable_mono (fun _ available => available)
          initialIncluded (initialReads index input inputMem)
      · apply callFamilyFrom occurrence injective initial initialReads rest
          restNodup (called :: available)
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
    {body : ModuleBody} {children : Children body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    (initial : Availability children)
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence children)
    (injective : Function.Injective occurrence)
    (fresh : ∀ index, occurrence index ∉ initial)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable initial
        (body.wiring.instanceInput (occurrence index).child input)) :
    Schedule body children inputAvailable
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
    {body : ModuleBody} {children : Children body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence children)
    (injective : Function.Injective occurrence)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable ([] : Availability children)
        (body.wiring.instanceInput (occurrence index).child input)) :
    Schedule body children inputAvailable
      (fun final =>
        (∀ index, occurrence index ∈ final) ∧
        ∀ called, called ∈ final → ∃ index, called = occurrence index) [] :=
  callFamilyFrom occurrence injective [] readsAvailable indices.values indices.nodup []
    (fun _ member => nomatch member)
    (fun _ _ member => nomatch member) _
    (fun _ _ covers only => ⟨
      (fun index => covers index
        (ListIndex.get_eq (indices.locate index) ▸ List.get_mem _ _)),
      (fun called member => by
        rcases only called member with impossible | found
        · cases impossible
        · rcases found with ⟨index, _, equal⟩
          exact ⟨index, equal⟩)⟩)

structure ReplayResult {body : ModuleBody} {children : Children body}
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (initial : Availability children)
    (sourceFinal : Availability children)
    (SourceFinish : Availability children → Prop) where
  final : Availability children
  schedule : Schedule body children inputAvailable (fun _ => True) initial
  final_eq : schedule.finalAvailability = final
  covered : ∀ occurrence, occurrence ∈ initial → occurrence ∈ final
  sourceFinished : SourceFinish sourceFinal
  sourceCovered : ∀ occurrence, occurrence ∈ sourceFinal → occurrence ∈ final

/-! Replay one schedule after an existing call sequence. Calls already present
in the target availability are omitted. The result remembers that every
previously available occurrence remains covered. -/

noncomputable def replay {body : ModuleBody} {children : Children body}
    {sourceInputs targetInputs : body.context.ports.inputs.Label → Prop}
    {Finish : Availability children → Prop}
    {sourceInitial targetInitial : Availability children}
    (schedule : Schedule body children sourceInputs Finish sourceInitial)
    (inputsMono : ∀ input, sourceInputs input → targetInputs input)
    (initialCovered : ∀ occurrence, occurrence ∈ sourceInitial →
      occurrence ∈ targetInitial) :
    ReplayResult targetInputs targetInitial schedule.finalAvailability Finish := by
  letI : DecidableEq (RuleOccurrence children) := RuleOccurrence.decidableEq
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

def CoversAllRules {body : ModuleBody} (children : Children body)
    (available : Availability children) : Prop :=
  ∀ child rule, RuleOccurrence.mk child rule ∈ available

theorem outputAvailable_of_covers
    {body : ModuleBody} {children : Children body}
    {available : Availability children}
    (covers : CoversAllRules children available)
    (child : body.context.instancePorts.Name)
    (output : (body.context.instancePorts.ports child).outputs.Label) :
    outputAvailable available child output := by
  have written := (children child).cycleContract.output_is_written output
  rw [ModuleCycleContract.writtenOutputs] at written
  rcases List.mem_flatMap.mp written with ⟨rule, ruleMem, outputMem⟩
  exact ⟨rule, covers child rule, outputMem⟩

theorem sourceAvailable_of_covers
    {body : ModuleBody} {children : Children body}
    {available : Availability children}
    (covers : CoversAllRules children available)
    (source : SignalSource body.context.ports body.context.instancePorts signalType) :
    sourceAvailable (fun _ => True) available source := by
  cases source with
  | moduleInput input => trivial
  | instanceOutput child output =>
      exact outputAvailable_of_covers covers child output

def BoundaryReady (body : ModuleBody) (children : Children body)
    (outputs : List body.context.ports.outputs.Label)
    (inputAvailable : body.context.ports.inputs.Label → Prop)
    (available : Availability children) : Prop :=
  ∀ output, output ∈ outputs →
    sourceAvailable inputAvailable available (body.wiring.moduleOutput output)

abbrev OutputSchedule (body : ModuleBody) (children : Children body)
    (contract : ModuleCycleContract body.context.ports)
    (name : contract.RuleName) :=
  let rule := (contract.outputRule name).2
  Schedule body children
    (fun input => input ∈ rule.readsInputs.labels)
    (BoundaryReady body children rule.writesOutputs.labels
      (fun input => input ∈ rule.readsInputs.labels)) []

def ChildrenStateInputsReady (body : ModuleBody) (children : Children body)
    (available : Availability children) : Prop :=
  ∀ child input,
    input ∈ (children child).cycleContract.stateRule.readsInputs.labels →
    sourceAvailable (fun _ => True) available
      (body.wiring.instanceInput child input)

abbrev StateSchedule (body : ModuleBody) (children : Children body) :=
  Schedule body children (fun _ => True)
    (ChildrenStateInputsReady body children) []

namespace StateSchedule

/-- A completed state schedule makes the inputs selected by every immediate
child state rule independent of the particular structural solution.  This is
the semantic reason for the state schedule's finish condition: scheduled
output rules determine every internal source needed by the next-state rules. -/
theorem childStateInputs_eq
    {body : ModuleBody} {children : Children body}
    (schedule : StateSchedule body children)
    (inputs : body.context.ports.inputs.Values)
    (currentState : (moduleStructure body children).State)
    (left right : (name : body.context.instancePorts.Name) →
      ProposedValues (children name).moduleStructure)
    (leftSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body (childStructure children)
        inputs left name)
      (currentState name) (left name))
    (rightSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body (childStructure children)
        inputs right name)
      (currentState name) (right name))
    (child : body.context.instancePorts.Name) :
    let selection := (children child).cycleContract.stateRule.readsInputs
    selection.project
        (ProposedValues.childInputs body (childStructure children)
          inputs left child) =
      selection.project
        (ProposedValues.childInputs body (childStructure children)
          inputs right child) := by
  dsimp
  apply SignalSelection.project_eq_of_eq_on
  intro input inputMem
  apply source_value_eq_of_available
    (schedule.finishAgreement inputs inputs (fun _ _ => rfl) currentState
      left right leftSatisfies rightSatisfies (by
        intro occurrence member
        contradiction))
    (fun _ => True) inputs inputs (fun _ _ => rfl)
    (body.wiring.instanceInput child input)
  exact schedule.finished child input inputMem

/-- Consequently, a child's public next-state rule produces the same value in
any two structural solutions with the same parent inputs and current state. -/
theorem childStateRuleApply_eq
    {body : ModuleBody} {children : Children body}
    (schedule : StateSchedule body children)
    (inputs : body.context.ports.inputs.Values)
    (currentState : (moduleStructure body children).State)
    (left right : (name : body.context.instancePorts.Name) →
      ProposedValues (children name).moduleStructure)
    (leftSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body (childStructure children)
        inputs left name)
      (currentState name) (left name))
    (rightSatisfies : ∀ name, (children name).moduleStructure.IsSolution
      (ProposedValues.childInputs body (childStructure children)
        inputs right name)
      (currentState name) (right name))
    (child : body.context.instancePorts.Name)
    (contractState : (children child).cycleContract.state.Values) :
    (children child).cycleContract.stateRule.apply
        (ProposedValues.childInputs body (childStructure children)
          inputs left child)
        contractState =
      (children child).cycleContract.stateRule.apply
        (ProposedValues.childInputs body (childStructure children)
          inputs right child)
        contractState := by
  unfold CycleStateRule.apply
  rw [schedule.childStateInputs_eq inputs currentState left right
    leftSatisfies rightSatisfies child]

end StateSchedule

structure RuleSchedules (body : ModuleBody) (children : Children body)
    (contract : ModuleCycleContract body.context.ports) where
  /-- One schedule establishing each parent output rule. -/
  output : ∀ name, OutputSchedule body children contract name
  /-- One schedule establishing the inputs needed by every child state rule. -/
  state : StateSchedule body children

namespace RuleSchedules

structure Combined (body : ModuleBody) (children : Children body) where
  schedule : Schedule body children (fun _ => True) (fun _ => True) []

def Combined.final (combined : Combined body children) : Availability children :=
  combined.schedule.finalAvailability

def Combined.empty (body : ModuleBody) (children : Children body) :
    Combined body children :=
  ⟨.done trivial⟩

noncomputable def Combined.add
    (combined : Combined body children)
    {sourceInputs : body.context.ports.inputs.Label → Prop}
    {Finish : Availability children → Prop}
    (next : Schedule body children sourceInputs Finish [])
    (inputsAvailable : ∀ input, sourceInputs input → True) :
    Combined body children := by
  let replayed := next.replay inputsAvailable
    (targetInitial := combined.final) (by intros; contradiction)
  exact ⟨combined.schedule.append replayed.schedule⟩

theorem Combined.add_preserves
    (combined : Combined body children)
    {sourceInputs : body.context.ports.inputs.Label → Prop}
    {Finish : Availability children → Prop}
    (next : Schedule body children sourceInputs Finish [])
    (inputsAvailable : ∀ input, sourceInputs input → True)
    (occurrence : RuleOccurrence children)
    (member : occurrence ∈ combined.final) :
    occurrence ∈ (combined.add next inputsAvailable).final := by
  let replayed := next.replay inputsAvailable
    (targetInitial := combined.final) (by intros; contradiction)
  have result := replayed.covered occurrence member
  rw [← replayed.final_eq] at result
  simpa [Combined.add, Combined.final, Schedule.finalAvailability_append,
    replayed] using result

theorem Combined.add_includes
    (combined : Combined body children)
    {sourceInputs : body.context.ports.inputs.Label → Prop}
    {Finish : Availability children → Prop}
    (next : Schedule body children sourceInputs Finish [])
    (inputsAvailable : ∀ input, sourceInputs input → True)
    (occurrence : RuleOccurrence children)
    (member : occurrence ∈ next.finalAvailability) :
    occurrence ∈ (combined.add next inputsAvailable).final := by
  let replayed := next.replay inputsAvailable
    (targetInitial := combined.final) (by intros; contradiction)
  have result := replayed.sourceCovered occurrence member
  rw [← replayed.final_eq] at result
  simpa [Combined.add, Combined.final, Schedule.finalAvailability_append,
    replayed] using result

noncomputable def combineOutputList
    (schedules : RuleSchedules body children contract) :
    List contract.RuleName → Combined body children
  | [] => Combined.empty body children
  | name :: rest =>
      (combineOutputList schedules rest).add (schedules.output name)
        (by intro input available; trivial)

noncomputable def combineOutputs
    (schedules : RuleSchedules body children contract) :
    Combined body children :=
  combineOutputList schedules contract.ruleNames.values

theorem mem_combineOutputList
    (schedules : RuleSchedules body children contract)
    (name : contract.RuleName) (nameMem : name ∈ names)
    (occurrence : RuleOccurrence children)
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
    (schedules : RuleSchedules body children contract)
    (name : contract.RuleName)
    (occurrence : RuleOccurrence children)
    (member : occurrence ∈ (schedules.output name).finalAvailability) :
    occurrence ∈ schedules.combineOutputs.final := by
  apply mem_combineOutputList schedules name
  · exact ListIndex.get_eq (contract.ruleNames.locate name) ▸ List.get_mem _ _
  · exact member

noncomputable def combined
    (schedules : RuleSchedules body children contract) :
    Combined body children :=
  schedules.combineOutputs |>.add schedules.state
    (by intro input available; trivial)

def CoversChildren (schedules : RuleSchedules body children contract) : Prop :=
  CoversAllRules children schedules.combined.final

theorem hasAtMostOneSolution
    (schedules : RuleSchedules body children contract)
    (covers : schedules.CoversChildren) :
    (moduleStructure body children).HasAtMostOneSolution := by
  intro inputs currentState left right leftSatisfies rightSatisfies
  rcases left with ⟨leftOutputs, leftChildren⟩
  rcases right with ⟨rightOutputs, rightChildren⟩
  change ProposedValues.boundaryOutputsSatisfy body (childStructure children)
      inputs leftOutputs leftChildren ∧ _ at leftSatisfies
  change ProposedValues.boundaryOutputsSatisfy body (childStructure children)
      inputs rightOutputs rightChildren ∧ _ at rightSatisfies
  have childOutputsAgree := schedules.combined.schedule.finishAgreement
    inputs inputs (fun _ _ => rfl) currentState leftChildren rightChildren
    leftSatisfies.2 rightSatisfies.2
    (by intro occurrence member; cases member)
  have childInputsEqual : ∀ name,
      ProposedValues.childInputs body (childStructure children)
          inputs leftChildren name =
        ProposedValues.childInputs body (childStructure children)
          inputs rightChildren name := by
    intro name
    funext input
    exact source_value_eq_of_available childOutputsAgree (fun _ => True)
      inputs inputs (fun _ _ => rfl) (body.wiring.instanceInput name input)
      (sourceAvailable_of_covers covers _)
  have childrenEqual : leftChildren = rightChildren := by
    funext name
    apply (children name).structuralResultUnique
    · exact leftSatisfies.2 name
    · rw [childInputsEqual name]
      exact rightSatisfies.2 name
  have outputsEqual : leftOutputs = rightOutputs := by
    funext output
    rw [leftSatisfies.1 output, rightSatisfies.1 output]
    exact source_value_eq_of_available childOutputsAgree (fun _ => True)
      inputs inputs (fun _ _ => rfl) (body.wiring.moduleOutput output)
      (sourceAvailable_of_covers covers _)
  cases outputsEqual
  cases childrenEqual
  rfl

end RuleSchedules

end Silean.Contracts.Cycle.Certification
