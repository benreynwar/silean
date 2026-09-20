import Silean.Semantics.StructuralRuleExistence

namespace Silean.ModuleStructuralCertification.Layer.ScheduleDerivation

open Silean

/-! # Kernel-checked support for structural schedule derivation

These lemmas are independent of behavioral contracts. The schedule elaborator
constructs applications of them; Lean's kernel checks the resulting local
availability and coverage evidence. -/

/-- A complete structural schedule, independent of any parent or child
behavioral contract. -/
structure DerivedCompleteSchedule (body : ModuleBody)
    (childRules : ChildRules body) where
  schedule : Schedule body childRules (fun _ => True) (fun _ => True) []
  coversAllRules : CoversAllRules body childRules schedule.finalAvailability

namespace DerivedCompleteSchedule

/-- Instantiate a complete derived schedule with certified children. -/
theorem certification
    (derived : DerivedCompleteSchedule body childRules)
    (children : ChildStructures body childRules) :
    ModuleStructuralCertification (moduleStructure body children) :=
  derived.schedule.certification children (fun _ => trivial)
    derived.coversAllRules

/-- Certify an independently declared composite whose children match the
certified children used by a complete structural schedule. -/
theorem certifyComposite
    (derived : DerivedCompleteSchedule body childRules)
    (structuralChildren : (child : body.instancePorts.Name) →
      ModuleStructure (body.instancePorts.ports child))
    (children : ChildStructures body childRules)
    (structuresMatch : ∀ child,
      (children child).moduleStructure = structuralChildren child) :
    ModuleStructuralCertification (.composite body structuralChildren) := by
  have equal : (fun child => (children child).moduleStructure) =
      structuralChildren := by
    funext child
    exact structuresMatch child
  exact ModuleStructuralCertification.transport
    (congrArg (ModuleStructure.composite body) equal)
    (derived.certification children)

end DerivedCompleteSchedule

/-- Turn one availability proof per declared read into the universal premise
required by `Schedule.call`. -/
theorem readsAvailable_of_certificates
    {body : ModuleBody} {childRules : ChildRules body}
    (inputAvailable : body.ports.inputs.Label → Prop)
    (available : Availability body childRules)
    (occurrence : RuleOccurrence body childRules)
    (certificates : DependentList (fun input => PLift
      (sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))) occurrence.reads) :
    ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input) := by
  letI : DecidableEq
      (body.instancePorts.ports occurrence.child).inputs.Label :=
    (body.instancePorts.ports occurrence.child).inputs.labels.decidableEq
  intro input member
  exact (certificates.get (ListIndex.ofMem member)).down

def moduleInputReadyBool
    {body : ModuleBody}
    (inputAvailable : body.ports.inputs.Label → Prop)
    (decideInput : ∀ input, Decidable (inputAvailable input))
    (input : body.ports.inputs.Label) : Bool :=
  @decide (inputAvailable input) (decideInput input)

theorem moduleInputAvailable_of_bool_eq_true
    {body : ModuleBody} {childRules : ChildRules body}
    (inputAvailable : body.ports.inputs.Label → Prop)
    (decideInput : ∀ input, Decidable (inputAvailable input))
    (available : Availability body childRules)
    (input : body.ports.inputs.Label)
    (ready : moduleInputReadyBool inputAvailable decideInput input = true) :
    sourceAvailable inputAvailable available (.moduleInput input) :=
  @of_decide_eq_true _ (decideInput input) ready

theorem enumerationValue_mem
    {alpha : Type} (enumeration : Enumeration alpha) (value : alpha) :
    value ∈ enumeration.values :=
  ListIndex.get_eq (enumeration.locate value) ▸ List.get_mem _ _

theorem signalLabel_mem_allGroup (signals : SignalMap)
    (label : signals.Label) : label ∈ (SignalGroup.all signals).labels := by
  rw [SignalGroup.all_labels]
  exact enumerationValue_mem signals.labels label

/-- If a structural interface has exactly one rule, output coverage says that
every child output is written by that rule. -/
theorem output_written_by_only_rule
    {body : ModuleBody} {childRules : ChildRules body}
    (child : body.instancePorts.Name)
    (rule : (childRules child).RuleName)
    (only : (childRules child).ruleNames.values = [rule])
    (output : (body.instancePorts.ports child).outputs.Label) :
    output ∈ (RuleOccurrence.mk child rule :
      RuleOccurrence body childRules).writes := by
  have written := (childRules child).output_is_written output
  rw [ModuleStructuralRules.writtenOutputs, only] at written
  simpa [RuleOccurrence.writes] using written

/-- Availability through a decidable wiring branch follows by checking both
branches. -/
theorem sourceAvailable_decidable_rec
    {body : ModuleBody} {childRules : ChildRules body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childRules}
    {signalType : SignalType} {condition : Prop}
    (whenFalse : ¬condition → SignalSource body.ports
      body.instancePorts signalType)
    (whenTrue : condition → SignalSource body.ports
      body.instancePorts signalType)
    (decision : Decidable condition)
    (falseAvailable : ∀ proof, sourceAvailable inputAvailable available
      (whenFalse proof))
    (trueAvailable : ∀ proof, sourceAvailable inputAvailable available
      (whenTrue proof)) :
    sourceAvailable inputAvailable available
      (@Decidable.rec condition
        (fun _ => SignalSource body.ports body.instancePorts signalType)
        whenFalse whenTrue decision) := by
  cases decision with
  | isFalse proof => exact falseAvailable proof
  | isTrue proof => exact trueAvailable proof

def childFreshBool
    {body : ModuleBody} {childRules : ChildRules body}
    (available : Availability body childRules)
    (occurrence : RuleOccurrence body childRules) : Bool :=
  letI := body.instancePorts.names.decidableEq
  decide (occurrence.child ∉ available.map RuleOccurrence.child)

theorem child_fresh_of_bool_eq_true
    {body : ModuleBody} {childRules : ChildRules body}
    (available : Availability body childRules)
    (occurrence : RuleOccurrence body childRules)
    (fresh : childFreshBool available occurrence = true) :
    occurrence.child ∉ available.map RuleOccurrence.child := by
  letI := body.instancePorts.names.decidableEq
  have fresh' : decide
      (occurrence.child ∉ available.map RuleOccurrence.child) = true := by
    simpa [childFreshBool] using fresh
  exact of_decide_eq_true fresh'

theorem fresh_of_child_bool_eq_true
    {body : ModuleBody} {childRules : ChildRules body}
    (available : Availability body childRules)
    (occurrence : RuleOccurrence body childRules)
    (fresh : childFreshBool available occurrence = true) :
    occurrence ∉ available := by
  have childFresh := child_fresh_of_bool_eq_true available occurrence fresh
  intro member
  exact childFresh (List.mem_map.mpr ⟨occurrence, member, rfl⟩)

theorem fresh_after_family
    {body : ModuleBody} {childRules : ChildRules body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    (initial : Availability body childRules)
    {Index : Type} (indices : Enumeration Index)
    (occurrence : Index → RuleOccurrence body childRules)
    (injective : Function.Injective occurrence)
    (fresh : ∀ index, occurrence index ∉ initial)
    (readsAvailable : ∀ index input, input ∈ (occurrence index).reads →
      sourceAvailable inputAvailable initial
        (body.wiring.instanceInput (occurrence index).child input))
    (candidate : RuleOccurrence body childRules)
    (oldFresh : candidate ∉ initial)
    (familyOccurrencesDifferent : ∀ index, candidate ≠ occurrence index) :
    candidate ∉ (Schedule.callFamilyAfter initial indices occurrence injective
      fresh readsAvailable).finalAvailability := by
  intro member
  rw [Schedule.mem_finalAvailability_callFamilyAfter_iff] at member
  rcases member with old | ⟨index, equal⟩
  · exact oldFresh old
  · exact familyOccurrencesDifferent index equal

theorem fresh_cons_of_child_disjoint
    {body : ModuleBody} {childRules : ChildRules body}
    (candidate head : RuleOccurrence body childRules)
    (tail : Availability body childRules)
    (different : candidate.child ≠ head.child)
    (freshTail : candidate ∉ tail) :
    candidate ∉ head :: tail := by
  intro member
  rcases List.mem_cons.mp member with equal | inTail
  · exact different (congrArg RuleOccurrence.child equal)
  · exact freshTail inTail

theorem fresh_cons_of_different
    {body : ModuleBody} {childRules : ChildRules body}
    (candidate head : RuleOccurrence body childRules)
    (tail : Availability body childRules)
    (different : candidate ≠ head)
    (freshTail : candidate ∉ tail) :
    candidate ∉ head :: tail := by
  intro member
  rcases List.mem_cons.mp member with equal | inTail
  · exact different equal
  · exact freshTail inTail

end Silean.ModuleStructuralCertification.Layer.ScheduleDerivation
