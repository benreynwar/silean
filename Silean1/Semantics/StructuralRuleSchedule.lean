import Silean.Semantics.StructuralDependency

namespace Silean.ModuleStructuralCertification.Layer

open Silean

/-! # Contract-independent structural rule schedules

Schedules mention only boundary dependency rules. Concrete child hierarchies
and proofs of those rules are supplied separately when deriving existence and
uniqueness. A schedule is proof data witnessing an acyclic evaluation order;
it is not stored in `ModuleStructure` and does not define circuit semantics. -/

/-- Structural rule interfaces required at the named child boundaries. -/
abbrev ChildRules (body : ModuleBody) :=
  (child : body.instancePorts.Name) →
    ModuleStructuralRules (body.instancePorts.ports child)

/-- Concrete child hierarchies certified against the declared structural
rules. -/
abbrev ChildStructures (body : ModuleBody) (childRules : ChildRules body) :=
  (child : body.instancePorts.Name) →
    ModuleStructuralCertifiedStructure (childRules child)

/-- Conservative structural interfaces for a family of children. -/
@[reducible] def wholeChildRules (body : ModuleBody) : ChildRules body :=
  fun child => ModuleStructuralRules.whole (body.instancePorts.ports child)

/-- Package a family of structurally certified children using their automatic
whole-module rules. -/
noncomputable def wholeCertifiedChildren
    (body : ModuleBody)
    (structures : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child))
    (certifications : ∀ child,
      ModuleStructuralCertification (structures child)) :
    ChildStructures body (wholeChildRules body) :=
  fun child => (certifications child).wholeCertifiedStructure

/-- The concrete composite obtained from structurally certified children. -/
abbrev moduleStructure (body : ModuleBody) {childRules : ChildRules body}
    (children : ChildStructures body childRules) : ModuleStructure body.ports :=
  .composite body fun child => (children child).moduleStructure

structure RuleOccurrence (body : ModuleBody) (childRules : ChildRules body) where
  child : body.instancePorts.Name
  rule : (childRules child).RuleName

namespace RuleOccurrence

@[reducible] instance : DecidableEq (RuleOccurrence body childRules) := by
  intro left right
  rcases left with ⟨leftChild, leftRule⟩
  rcases right with ⟨rightChild, rightRule⟩
  letI : DecidableEq body.instancePorts.Name :=
    body.instancePorts.names.decidableEq
  if childEqual : leftChild = rightChild then
    subst rightChild
    letI : DecidableEq (childRules leftChild).RuleName :=
      (childRules leftChild).ruleNames.decidableEq
    if ruleEqual : leftRule = rightRule then
      subst rightRule
      exact isTrue rfl
    else
      exact isFalse fun equal => ruleEqual (by injection equal)
  else
    exact isFalse fun equal => childEqual (by injection equal)

def writes (occurrence : RuleOccurrence body childRules) :
    List (body.instancePorts.ports occurrence.child).outputs.Label :=
  (childRules occurrence.child).rule occurrence.rule |>.writes

def reads (occurrence : RuleOccurrence body childRules) :
    List (body.instancePorts.ports occurrence.child).inputs.Label :=
  (childRules occurrence.child).rule occurrence.rule |>.reads

end RuleOccurrence

abbrev Availability (body : ModuleBody) (childRules : ChildRules body) :=
  List (RuleOccurrence body childRules)

/-- Every structural output rule of every child has been scheduled. -/
def CoversAllRules (body : ModuleBody) (childRules : ChildRules body)
    (available : Availability body childRules) : Prop :=
  ∀ child rule, RuleOccurrence.mk child rule ∈ available

def outputAvailable
    (available : Availability body childRules)
    (child : body.instancePorts.Name)
    (output : (body.instancePorts.ports child).outputs.Label) : Prop :=
  ∃ rule, RuleOccurrence.mk child rule ∈ available ∧
    output ∈ (RuleOccurrence.mk child rule : RuleOccurrence body childRules).writes

def sourceAvailable
    (inputAvailable : body.ports.inputs.Label → Prop)
    (available : Availability body childRules)
    (source : SignalSource body.ports body.instancePorts signalType) : Prop :=
  match source with
  | .moduleInput input => inputAvailable input
  | .instanceOutput child output => outputAvailable available child output

@[simp] theorem sourceAvailable_castType
    (inputAvailable : body.ports.inputs.Label → Prop)
    (available : Availability body childRules)
    (equal : sourceType = targetType)
    (source : SignalSource body.ports body.instancePorts sourceType) :
    sourceAvailable inputAvailable available
        (SignalSource.castType equal source) ↔
      sourceAvailable inputAvailable available source := by
  cases equal
  rfl

@[simp] theorem sourceAvailable_moduleInput
    (inputAvailable : body.ports.inputs.Label → Prop)
    (available : Availability body childRules)
    (input : body.ports.inputs.Label) :
    sourceAvailable inputAvailable available (.moduleInput input) =
      inputAvailable input := rfl

@[simp] theorem sourceAvailable_instanceOutput
    (inputAvailable : body.ports.inputs.Label → Prop)
    (available : Availability body childRules)
    (child : body.instancePorts.Name)
    (output : (body.instancePorts.ports child).outputs.Label) :
    sourceAvailable inputAvailable available (.instanceOutput child output) =
      outputAvailable available child output := rfl

theorem sourceAvailable_of_instanceOutput
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childRules}
    {child : body.instancePorts.Name}
    {rule : (childRules child).RuleName}
    {output : (body.instancePorts.ports child).outputs.Label}
    (called : RuleOccurrence.mk child rule ∈ available)
    (written : output ∈
      (RuleOccurrence.mk child rule : RuleOccurrence body childRules).writes) :
    sourceAvailable inputAvailable available (.instanceOutput child output) :=
  ⟨rule, called, written⟩

theorem outputAvailable_of_covers
    {available : Availability body childRules}
    (covers : CoversAllRules body childRules available)
    (child : body.instancePorts.Name)
    (output : (body.instancePorts.ports child).outputs.Label) :
    outputAvailable available child output := by
  have written := (childRules child).output_is_written output
  rw [ModuleStructuralRules.writtenOutputs] at written
  rcases List.mem_flatMap.mp written with ⟨rule, _, outputMem⟩
  exact ⟨rule, covers child rule, outputMem⟩

theorem sourceAvailable_of_covers
    {available : Availability body childRules}
    (covers : CoversAllRules body childRules available)
    (source : SignalSource body.ports body.instancePorts signalType) :
    sourceAvailable (fun _ => True) available source := by
  cases source with
  | moduleInput _ => trivial
  | instanceOutput child output => exact outputAvailable_of_covers covers child output

theorem sourceAvailable_mono
    {leftInputs rightInputs : body.ports.inputs.Label → Prop}
    {left right : Availability body childRules}
    (inputsMono : ∀ input, leftInputs input → rightInputs input)
    (availableMono : ∀ occurrence, occurrence ∈ left → occurrence ∈ right)
    {source : SignalSource body.ports body.instancePorts signalType}
    (available : sourceAvailable leftInputs left source) :
    sourceAvailable rightInputs right source := by
  cases source with
  | moduleInput input => exact inputsMono input available
  | instanceOutput child output =>
      rcases available with ⟨rule, called, written⟩
      exact ⟨rule, availableMono _ called, written⟩

/-- A proof-bearing topological order of child structural-rule calls. -/
inductive Schedule (body : ModuleBody) (childRules : ChildRules body)
    (inputAvailable : body.ports.inputs.Label → Prop)
    (Finish : Availability body childRules → Prop) :
    Availability body childRules → Type 1
  | done {available} (finished : Finish available) :
      Schedule body childRules inputAvailable Finish available
  | call {available}
      (occurrence : RuleOccurrence body childRules)
      (readsAvailable : ∀ input, input ∈ occurrence.reads →
        sourceAvailable inputAvailable available
          (body.wiring.instanceInput occurrence.child input))
      (fresh : occurrence ∉ available)
      (rest : Schedule body childRules inputAvailable Finish
        (occurrence :: available)) :
      Schedule body childRules inputAvailable Finish available

namespace Schedule

def finalAvailability
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    {initial : Availability body childRules} :
    Schedule body childRules inputAvailable Finish initial →
      Availability body childRules
  | .done (available := available) _ => available
  | .call _ _ _ rest => rest.finalAvailability

@[simp] theorem finalAvailability_done
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    {available : Availability body childRules}
    (finished : Finish available) :
    finalAvailability (.done finished :
      Schedule body childRules inputAvailable Finish available) = available := rfl

@[simp] theorem finalAvailability_call
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    {available : Availability body childRules}
    (occurrence : RuleOccurrence body childRules)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (fresh : occurrence ∉ available)
    (rest : Schedule body childRules inputAvailable Finish
      (occurrence :: available)) :
    finalAvailability (.call occurrence readsAvailable fresh rest) =
      finalAvailability rest := rfl

noncomputable def append
    {inputAvailable : body.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (first : Schedule body childRules inputAvailable FirstFinish initial)
    (second : Schedule body childRules inputAvailable SecondFinish
      first.finalAvailability) :
    Schedule body childRules inputAvailable SecondFinish initial := by
  induction first with
  | done _ => exact second
  | call occurrence readsAvailable fresh rest induction =>
      exact .call occurrence readsAvailable fresh (induction second)

@[simp] theorem finalAvailability_append
    {inputAvailable : body.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (first : Schedule body childRules inputAvailable FirstFinish initial)
    (second : Schedule body childRules inputAvailable SecondFinish
      first.finalAvailability) :
    (first.append second).finalAvailability = second.finalAvailability := by
  induction first with
  | done _ => rfl
  | call _ _ _ _ induction => exact induction second

/-! Call one rule for every member of a finite family. All reads must already
be available before the family starts, so enumeration order is irrelevant. -/

private noncomputable def callFamilyFrom
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Index : Type} (occurrence : Index → RuleOccurrence body childRules)
    (injective : Function.Injective occurrence)
    (initial : Availability body childRules)
    (initialReads : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable initial
        (body.wiring.instanceInput (occurrence index).child input))
    (remaining : List Index) (remainingNodup : remaining.Nodup)
    (available : Availability body childRules)
    (initialIncluded : ∀ called, called ∈ initial → called ∈ available)
    (fresh : ∀ index, index ∈ remaining → occurrence index ∉ available)
    (Finish : Availability body childRules → Prop)
    (finish : ∀ final,
      (∀ called, called ∈ available → called ∈ final) →
      (∀ index, index ∈ remaining → occurrence index ∈ final) →
      (∀ called, called ∈ final →
        called ∈ available ∨ ∃ index, index ∈ remaining ∧ called = occurrence index) →
      Finish final) :
    Schedule body childRules inputAvailable Finish available :=
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
    {inputAvailable : body.ports.inputs.Label → Prop}
    (initial : Availability body childRules)
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence body childRules)
    (injective : Function.Injective occurrence)
    (fresh : ∀ index, occurrence index ∉ initial)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable initial
        (body.wiring.instanceInput (occurrence index).child input)) :
    Schedule body childRules inputAvailable
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
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence body childRules)
    (injective : Function.Injective occurrence)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable ([] : Availability body childRules)
        (body.wiring.instanceInput (occurrence index).child input)) :
    Schedule body childRules inputAvailable
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
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (schedule : Schedule body childRules inputAvailable Finish initial) :
    Finish schedule.finalAvailability := by
  induction schedule with
  | done finished => exact finished
  | call _ _ _ _ induction => exact induction

@[simp] theorem mem_finalAvailability_callFamilyAfter_iff
    {inputAvailable : body.ports.inputs.Label → Prop}
    (initial : Availability body childRules)
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence body childRules)
    (injective : Function.Injective occurrence)
    (fresh : ∀ index, occurrence index ∉ initial)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable initial
        (body.wiring.instanceInput (occurrence index).child input))
    (called : RuleOccurrence body childRules) :
    called ∈ (callFamilyAfter initial indices occurrence injective fresh
      readsAvailable).finalAvailability ↔
      called ∈ initial ∨ ∃ index, called = occurrence index := by
  let family := callFamilyAfter initial indices occurrence injective fresh
    readsAvailable
  constructor
  · exact family.finished.2.2 called
  · intro member
    rcases member with old | ⟨index, equal⟩
    · exact family.finished.1 called old
    · rw [equal]
      exact family.finished.2.1 index

theorem initial_mem_final
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (schedule : Schedule body childRules inputAvailable Finish initial)
    (occurrence : RuleOccurrence body childRules) (member : occurrence ∈ initial) :
    occurrence ∈ schedule.finalAvailability := by
  induction schedule with
  | done _ => exact member
  | call called _ _ _ induction =>
      exact induction (List.mem_cons_of_mem called member)

/-! ## Ordered families

`callFamilyAfter` is deliberately order-insensitive: every family member must
be ready before the family starts.  Linear pipelines and other acyclic chains
instead need later members to see the outputs of earlier members. -/

/-- Call an explicit duplicate-free list in order.  The read obligation for a
member is stated against the reverse of its chronological prefix because
`Availability` stores the most recently called rule first. -/
noncomputable def callListAfter
    {inputAvailable : body.ports.inputs.Label → Prop}
    (initial : Availability body childRules)
    (ordered : List (RuleOccurrence body childRules))
    (allNodup : (ordered.reverse ++ initial).Nodup)
    (readsAvailable : ∀ before occurrence suffix,
      ordered = before ++ occurrence :: suffix →
      ∀ input, input ∈ occurrence.reads →
        sourceAvailable inputAvailable (before.reverse ++ initial)
          (body.wiring.instanceInput occurrence.child input)) :
    Schedule body childRules inputAvailable
      (fun final => final = ordered.reverse ++ initial) initial := by
  induction ordered generalizing initial with
  | nil =>
      exact .done (by simp)
  | cons occurrence rest induction =>
      have extendedNodup : (rest.reverse ++ occurrence :: initial).Nodup := by
        simpa [List.reverse_cons, List.append_assoc] using allNodup
      refine .call occurrence ?_ ?_ ?_
      · intro input member
        exact readsAvailable [] occurrence rest rfl input member
      · exact (List.nodup_append.mp extendedNodup).2.1 |>
          List.nodup_cons.mp |>.1
      · have tailReads : ∀ before selected suffix,
            rest = before ++ selected :: suffix →
            ∀ input, input ∈ selected.reads →
              sourceAvailable inputAvailable
                (before.reverse ++ occurrence :: initial)
                (body.wiring.instanceInput selected.child input) := by
          intro before selected suffix equal input member
          have original : occurrence :: rest =
              (occurrence :: before) ++ selected :: suffix := by
            simp only [List.cons_append]
            rw [equal]
          simpa [List.reverse_cons, List.append_assoc] using
            readsAvailable (occurrence :: before) selected suffix original
              input member
        simpa [List.reverse_cons, List.append_assoc] using
          induction (occurrence :: initial) extendedNodup tailReads

/-- Call every member of an enumeration sequentially.  Each member may read
outputs of precisely the members preceding its constructive enumeration
position. -/
noncomputable def callSequentialFamilyAfter
    {inputAvailable : body.ports.inputs.Label → Prop}
    (initial : Availability body childRules)
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence body childRules)
    (injective : Function.Injective occurrence)
    (allNodup : (indices.values.reverse.map occurrence ++ initial).Nodup)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable
        ((indices.locate index).preceding.reverse.map occurrence ++ initial)
        (body.wiring.instanceInput (occurrence index).child input)) :
    Schedule body childRules inputAvailable
      (fun final => final = indices.values.reverse.map occurrence ++ initial)
      initial := by
  have listNodup :
      ((indices.values.map occurrence).reverse ++ initial).Nodup := by
    simpa [List.map_reverse] using allNodup
  have mappedNodup : (indices.values.map occurrence).Nodup :=
    List.nodup_map_of_injective occurrence injective indices.nodup
  have listReads : ∀ before called suffix,
      indices.values.map occurrence = before ++ called :: suffix →
      ∀ input, input ∈ called.reads →
        sourceAvailable inputAvailable (before.reverse ++ initial)
          (body.wiring.instanceInput called.child input) := by
    intro before called suffix orderedEqual input member
    have calledMem : called ∈ indices.values.map occurrence := by
      rw [orderedEqual]
      simp
    rcases List.mem_map.mp calledMem with
      ⟨index, _, indexEqual⟩
    subst called
    let sourceIndex : ListIndex index indices.values := indices.locate index
    let mappedIndex : ListIndex (occurrence index)
        (indices.values.map occurrence) := sourceIndex.map occurrence
    let explicitIndex : ListIndex (occurrence index)
        (before ++ occurrence index :: suffix) :=
      (.head : ListIndex (occurrence index) (occurrence index :: suffix))
        |>.prependMany before
    have precedingEqual :
        mappedIndex.preceding = before := by
      have transported := ListIndex.preceding_eq_of_list_eq
        orderedEqual mappedNodup mappedIndex explicitIndex
      calc
        mappedIndex.preceding = explicitIndex.preceding := transported
        _ = before := by
          exact ListIndex.preceding_prependMany_head before
            (occurrence index) suffix
    have sourcePrecedingEqual :
        sourceIndex.preceding.map occurrence = before := by
      calc
        sourceIndex.preceding.map occurrence =
            (sourceIndex.map occurrence).preceding :=
          (ListIndex.preceding_map occurrence sourceIndex).symm
        _ = mappedIndex.preceding := rfl
        _ = before := precedingEqual
    have availabilityEqual :
        sourceIndex.preceding.reverse.map occurrence = before.reverse := by
      simpa [List.map_reverse] using congrArg List.reverse sourcePrecedingEqual
    have childReads := readsAvailable index input member
    change sourceAvailable inputAvailable
      (sourceIndex.preceding.reverse.map occurrence ++ initial)
      (body.wiring.instanceInput (occurrence index).child input) at childReads
    rw [availabilityEqual] at childReads
    exact childReads
  simpa [List.map_reverse] using
    callListAfter (inputAvailable := inputAvailable) initial
      (indices.values.map occurrence) listNodup listReads

/-- A family member with a smaller enumeration ordinal is available before a
later member in a sequential family. -/
theorem occurrence_mem_preceding_of_ordinal_lt
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence body childRules)
    (earlier later : Index)
    (before : indices.ordinal earlier < indices.ordinal later) :
    occurrence earlier ∈
      (indices.locate later).preceding.reverse.map occurrence := by
  apply List.mem_map.mpr
  refine ⟨earlier, ?_, rfl⟩
  simp only [List.mem_reverse]
  exact ListIndex.mem_preceding_of_toFin_lt
    (indices.locate earlier) (indices.locate later) before

/-- Change only the terminal obligation of a schedule. -/
noncomputable def mapFinish
    {inputAvailable : body.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (schedule : Schedule body childRules inputAvailable FirstFinish initial)
    (implies : ∀ available, FirstFinish available → SecondFinish available) :
    Schedule body childRules inputAvailable SecondFinish initial := by
  induction schedule with
  | done finished => exact .done (implies _ finished)
  | call occurrence readsAvailable fresh rest induction =>
      exact .call occurrence readsAvailable fresh induction

@[simp] theorem finalAvailability_mapFinish
    {inputAvailable : body.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (schedule : Schedule body childRules inputAvailable FirstFinish initial)
    (implies : ∀ available, FirstFinish available → SecondFinish available) :
    (schedule.mapFinish implies).finalAvailability =
      schedule.finalAvailability := by
  induction schedule with
  | done _ => rfl
  | call _ _ _ _ induction => exact induction

/-- Replace the terminal obligation with a fact about the actual final
availability. -/
noncomputable def replaceFinish
    {inputAvailable : body.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (schedule : Schedule body childRules inputAvailable FirstFinish initial)
    (finished : SecondFinish schedule.finalAvailability) :
    Schedule body childRules inputAvailable SecondFinish initial := by
  induction schedule with
  | done _ => exact .done finished
  | call occurrence readsAvailable fresh rest induction =>
      exact .call occurrence readsAvailable fresh (induction finished)

end Schedule

end Silean.ModuleStructuralCertification.Layer
