import Silean.Contracts.Cycle.CycleImplementation
import Silean.Semantics.StructuralRuleSchedule

namespace Silean.Contracts.Cycle.Certification.Layer

open Silean

/-! # Cycle-layer views of contract-independent structural schedules

The canonical schedule machinery lives under
`ModuleStructuralCertification.Layer`. A cycle contract contributes only its
boundary structural-rule specifications; the cycle-specific types below add
parent output/state scheduling obligations used by behavioral certification.
Existing cycle authoring syntax is intentionally preserved. -/

/-- Dependency-only child interfaces obtained from the declared cycle
contracts. -/
@[reducible] def childStructuralRules (body : ModuleBody)
    (childContracts : ChildCycleContracts body) :
    ModuleStructuralCertification.Layer.ChildRules body :=
  fun child => (childContracts child).structuralRules

abbrev RuleOccurrence (body : ModuleBody)
    (childContracts : ChildCycleContracts body) :=
  ModuleStructuralCertification.Layer.RuleOccurrence body
    (childStructuralRules body childContracts)

namespace RuleOccurrence

@[match_pattern] abbrev mk
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (child : body.instancePorts.Name)
    (rule : (childContracts child).RuleName) :
    RuleOccurrence body childContracts :=
  ModuleStructuralCertification.Layer.RuleOccurrence.mk child rule

abbrev child {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (occurrence : RuleOccurrence body childContracts) :
    body.instancePorts.Name :=
  ModuleStructuralCertification.Layer.RuleOccurrence.child occurrence

abbrev rule {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (occurrence : RuleOccurrence body childContracts) :
    (childContracts
      (ModuleStructuralCertification.Layer.RuleOccurrence.child occurrence)).RuleName :=
  ModuleStructuralCertification.Layer.RuleOccurrence.rule occurrence

abbrev writes (occurrence : RuleOccurrence body childContracts) :=
  ModuleStructuralCertification.Layer.RuleOccurrence.writes occurrence

abbrev reads (occurrence : RuleOccurrence body childContracts) :=
  ModuleStructuralCertification.Layer.RuleOccurrence.reads occurrence

end RuleOccurrence

abbrev Availability (body : ModuleBody)
    (childContracts : ChildCycleContracts body) :=
  ModuleStructuralCertification.Layer.Availability body
    (childStructuralRules body childContracts)

abbrev CoversAllRules (body : ModuleBody)
    (childContracts : ChildCycleContracts body)
    (available : Availability body childContracts) :=
  ModuleStructuralCertification.Layer.CoversAllRules body
    (childStructuralRules body childContracts) available

abbrev outputAvailable
    (available : Availability body childContracts)
    (child : body.instancePorts.Name)
    (output : (body.instancePorts.ports child).outputs.Label) :=
  ModuleStructuralCertification.Layer.outputAvailable available child output

abbrev sourceAvailable
    (inputAvailable : body.ports.inputs.Label → Prop)
    (available : Availability body childContracts)
    (source : SignalSource body.ports body.instancePorts signalType) :=
  ModuleStructuralCertification.Layer.sourceAvailable inputAvailable available source

theorem sourceAvailable_castType
    (inputAvailable : body.ports.inputs.Label → Prop)
    (available : Availability body childContracts)
    (equal : sourceType = targetType)
    (source : SignalSource body.ports body.instancePorts sourceType) :
    sourceAvailable inputAvailable available
        (SignalSource.castType equal source) ↔
      sourceAvailable inputAvailable available source :=
  ModuleStructuralCertification.Layer.sourceAvailable_castType
    inputAvailable available equal source

theorem sourceAvailable_of_instanceOutput
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childContracts}
    {child : body.instancePorts.Name}
    {rule : (childContracts child).RuleName}
    {output : (body.instancePorts.ports child).outputs.Label}
    (called : RuleOccurrence.mk child rule ∈ available)
    (written : output ∈
      (RuleOccurrence.mk child rule : RuleOccurrence body childContracts).writes) :
    sourceAvailable inputAvailable available (.instanceOutput child output) :=
  ModuleStructuralCertification.Layer.sourceAvailable_of_instanceOutput
    called written

theorem outputAvailable_of_covers
    {available : Availability body childContracts}
    (covers : CoversAllRules body childContracts available)
    (child : body.instancePorts.Name)
    (output : (body.instancePorts.ports child).outputs.Label) :
    outputAvailable available child output :=
  ModuleStructuralCertification.Layer.outputAvailable_of_covers
    covers child output

theorem sourceAvailable_of_covers
    {available : Availability body childContracts}
    (covers : CoversAllRules body childContracts available)
    (source : SignalSource body.ports body.instancePorts signalType) :
    sourceAvailable (fun _ => True) available source :=
  ModuleStructuralCertification.Layer.sourceAvailable_of_covers covers source

theorem sourceAvailable_mono
    {leftInputs rightInputs : body.ports.inputs.Label → Prop}
    {left right : Availability body childContracts}
    (inputsMono : ∀ input, leftInputs input → rightInputs input)
    (availableMono : ∀ occurrence, occurrence ∈ left → occurrence ∈ right)
    {source : SignalSource body.ports body.instancePorts signalType}
    (available : sourceAvailable leftInputs left source) :
    sourceAvailable rightInputs right source :=
  ModuleStructuralCertification.Layer.sourceAvailable_mono
    inputsMono availableMono available

abbrev Schedule (body : ModuleBody)
    (childContracts : ChildCycleContracts body)
    (inputAvailable : body.ports.inputs.Label → Prop)
    (Finish : Availability body childContracts → Prop)
    (initial : Availability body childContracts) :=
  ModuleStructuralCertification.Layer.Schedule body
    (childStructuralRules body childContracts) inputAvailable Finish initial

namespace Schedule

abbrev done
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {available : Availability body childContracts}
    (finished : Finish available) :
    Schedule body childContracts inputAvailable Finish available :=
  ModuleStructuralCertification.Layer.Schedule.done finished

abbrev call
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {available : Availability body childContracts}
    (occurrence : RuleOccurrence body childContracts)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (fresh : occurrence ∉ available)
    (rest : Schedule body childContracts inputAvailable Finish
      (occurrence :: available)) :
    Schedule body childContracts inputAvailable Finish available :=
  ModuleStructuralCertification.Layer.Schedule.call
    occurrence readsAvailable fresh rest

abbrev finalAvailability
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable Finish initial) :
    Availability body childContracts :=
  ModuleStructuralCertification.Layer.Schedule.finalAvailability schedule

@[simp] theorem finalAvailability_done
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {available : Availability body childContracts}
    (finished : Finish available) :
    finalAvailability (.done finished :
      Schedule body childContracts inputAvailable Finish available) = available := rfl

@[simp] theorem finalAvailability_call
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
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

noncomputable abbrev append
    {body : ModuleBody} {children : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body children → Prop}
    {initial : Availability body children}
    (first : Schedule body children inputAvailable FirstFinish initial)
    (second : Schedule body children inputAvailable SecondFinish
      first.finalAvailability) :
    Schedule body children inputAvailable SecondFinish initial :=
  ModuleStructuralCertification.Layer.Schedule.append first second

@[simp] theorem finalAvailability_append
    {body : ModuleBody} {children : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body children → Prop}
    {initial : Availability body children}
    (first : Schedule body children inputAvailable FirstFinish initial)
    (second : Schedule body children inputAvailable SecondFinish
      first.finalAvailability) :
    (first.append second).finalAvailability = second.finalAvailability :=
  ModuleStructuralCertification.Layer.Schedule.finalAvailability_append first second

noncomputable abbrev callFamilyAfter
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
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
  ModuleStructuralCertification.Layer.Schedule.callFamilyAfter
    initial indices occurrence injective fresh readsAvailable

noncomputable abbrev callFamily
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
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
  ModuleStructuralCertification.Layer.Schedule.callFamily
    indices occurrence injective readsAvailable

theorem finished
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable Finish initial) :
    Finish schedule.finalAvailability :=
  ModuleStructuralCertification.Layer.Schedule.finished schedule

theorem initial_mem_final
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable Finish initial)
    (occurrence : RuleOccurrence body childContracts) (member : occurrence ∈ initial) :
    occurrence ∈ schedule.finalAvailability :=
  ModuleStructuralCertification.Layer.Schedule.initial_mem_final
    schedule occurrence member

@[simp] theorem mem_finalAvailability_callFamilyAfter_iff
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
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
      called ∈ initial ∨ ∃ index, called = occurrence index :=
  ModuleStructuralCertification.Layer.Schedule.mem_finalAvailability_callFamilyAfter_iff
    initial indices occurrence injective fresh readsAvailable called

noncomputable abbrev mapFinish
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable FirstFinish initial)
    (implies : ∀ available, FirstFinish available → SecondFinish available) :
    Schedule body childContracts inputAvailable SecondFinish initial :=
  ModuleStructuralCertification.Layer.Schedule.mapFinish schedule implies

noncomputable abbrev replaceFinish
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {FirstFinish SecondFinish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable FirstFinish initial)
    (finished : SecondFinish schedule.finalAvailability) :
    Schedule body childContracts inputAvailable SecondFinish initial :=
  ModuleStructuralCertification.Layer.Schedule.replaceFinish schedule finished

end Schedule

def BoundaryReady (body : ModuleBody) (childContracts : ChildCycleContracts body)
    (outputs : List body.ports.outputs.Label)
    (inputAvailable : body.ports.inputs.Label → Prop)
    (available : Availability body childContracts) : Prop :=
  ∀ output, output ∈ outputs →
    sourceAvailable inputAvailable available (body.wiring.moduleOutput output)

abbrev OutputSchedule (body : ModuleBody)
    (childContracts : ChildCycleContracts body)
    (contract : ModuleCycleContract body.ports)
    (name : contract.RuleName) :=
  let rule := contract.outputRule name
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
    (contract : ModuleCycleContract body.ports) where
  output : ∀ name, OutputSchedule body childContracts contract name
  state : StateSchedule body childContracts

namespace RuleSchedules

def CoversChildren (schedules : RuleSchedules body childContracts contract) : Prop :=
  ∀ child rule,
    RuleOccurrence.mk child rule ∈ schedules.state.finalAvailability ∨
      ∃ parentRule, RuleOccurrence.mk child rule ∈
        (schedules.output parentRule).finalAvailability

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
