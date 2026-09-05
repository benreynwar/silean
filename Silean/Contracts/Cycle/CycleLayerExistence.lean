import Silean.Contracts.Cycle.CycleLayerSemantics
import Silean.Semantics.StructuralExecution

namespace Silean.Contracts.Cycle.Certification.Layer

open Silean

/-! # Internal construction semantics for a rule schedule

`Schedule` is propositionally checked proof data.  This file gives that proof
data a private proof evaluator: each call applies one public child contract
rule and stores the values written by that occurrence. The evaluator is used only to
prove that structural solutions exist; it is not stored in a module structure
or exposed as the meaning of hardware, and it is not stored in a certification.
Module proofs use the generic theorems in `CycleLayerConstruction`.
-/

/-- A scheduled occurrence records a complete output map for its child. Only
the occurrence's declared writes carry meaningful values; using a complete map
keeps later typed lookup independent of the rule's existential shape. -/
abbrev RuleOccurrence.Values {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (occurrence : RuleOccurrence body childContracts) :=
  (body.context.instancePorts.ports occurrence.child).outputs.Values

/-- Values corresponding position-for-position to scheduled occurrences. -/
abbrev Availability.Values {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (available : Availability body childContracts) :=
  DependentList (@RuleOccurrence.Values body childContracts) available

namespace Availability.Values

/-- Retrieve the values stored for an occurrence known to be available. -/
noncomputable def get {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {available : Availability body childContracts}
    (values : available.Values) (occurrence : RuleOccurrence body childContracts)
    (member : occurrence ∈ available) : occurrence.Values := by
  letI : DecidableEq (RuleOccurrence body childContracts) := inferInstance
  exact DependentList.get values (ListIndex.ofMem member)

@[simp] theorem get_cons_self {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (occurrence : RuleOccurrence body childContracts) (value : occurrence.Values)
    {available : Availability body childContracts} (values : available.Values)
    (member : occurrence ∈ occurrence :: available) :
    get (.cons value values) occurrence member = value := by
  unfold get
  simp only [ListIndex.ofMem_cons_self]
  rfl

theorem get_cons_of_ne {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {occurrence head : RuleOccurrence body childContracts}
    (different : occurrence ≠ head) (value : head.Values)
    {available : Availability body childContracts} (values : available.Values)
    (member : occurrence ∈ available) :
    get (.cons value values) occurrence (List.mem_cons_of_mem head member) =
      get values occurrence member := by
  letI : DecidableEq (RuleOccurrence body childContracts) := inferInstance
  unfold get
  rw [ListIndex.ofMem_cons_of_ne different]
  simp only [DependentList.get]
  exact member

theorem get_output_eq_of_both_write
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {available : Availability body childContracts} (values : available.Values)
    (child : body.context.instancePorts.Name)
    {left right : (childContracts child).RuleName}
    (leftMem : Layer.RuleOccurrence.mk child left ∈ available)
    (rightMem : Layer.RuleOccurrence.mk child right ∈ available)
    (output : (body.context.instancePorts.ports child).outputs.Label)
    (leftWrites : output ∈
      (Layer.RuleOccurrence.mk child left : RuleOccurrence body childContracts).writes)
    (rightWrites : output ∈
      (Layer.RuleOccurrence.mk child right : RuleOccurrence body childContracts).writes) :
    values.get ⟨child, left⟩ leftMem output =
      values.get ⟨child, right⟩ rightMem output := by
  have equal := (childContracts child).rule_eq_of_both_write
    leftWrites rightWrites
  change left = right at equal
  subst right
  rfl

/-- Read a total output map for every child once the availability covers every
child rule. -/
noncomputable def childOutputs {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {available : Availability body childContracts} (values : available.Values)
    (covers : CoversAllRules body childContracts available) :
    (child : body.context.instancePorts.Name) →
      (body.context.instancePorts.ports child).outputs.Values :=
  fun child output =>
    let availableOutput := outputAvailable_of_covers covers child output
    let rule := Classical.choose availableOutput
    let facts := Classical.choose_spec availableOutput
    values.get ⟨child, rule⟩ facts.1 output

/-- Read a structurally wired source from root inputs and the values produced
by earlier rule calls. -/
noncomputable def sourceValue {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {available : Availability body childContracts}
    (values : available.Values)
    (inputs : body.context.ports.inputs.Values)
    (source : SignalSource body.context.ports body.context.instancePorts signalType)
    (isAvailable : sourceAvailable inputAvailable available source) :
    signalType.Denote := by
  cases source with
  | moduleInput input => exact inputs input
  | instanceOutput child output =>
      let rule := Classical.choose isAvailable
      have availableAndWritten := Classical.choose_spec isAvailable
      exact values.get ⟨child, rule⟩ availableAndWritten.1 output

theorem sourceValue_eq_childOutputs
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {available : Availability body childContracts}
    (values : available.Values) (covers : CoversAllRules body childContracts available)
    (inputs : body.context.ports.inputs.Values)
    (source : SignalSource body.context.ports body.context.instancePorts signalType)
    (isAvailable : sourceAvailable inputAvailable available source) :
    values.sourceValue inputs source isAvailable =
      source.value inputs (values.childOutputs covers) := by
  cases source with
  | moduleInput input => rfl
  | instanceOutput child output =>
      let leftRule := Classical.choose isAvailable
      have leftFacts := Classical.choose_spec isAvailable
      let rightAvailable := outputAvailable_of_covers covers child output
      let rightRule := Classical.choose rightAvailable
      have rightFacts := Classical.choose_spec rightAvailable
      exact values.get_output_eq_of_both_write child
        leftFacts.1 rightFacts.1 output leftFacts.2 rightFacts.2

theorem sourceValue_instanceOutput_eq
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {available : Availability body childContracts}
    (values : available.Values) (inputs : body.context.ports.inputs.Values)
    (child : body.context.instancePorts.Name)
    (output : (body.context.instancePorts.ports child).outputs.Label)
    (isAvailable : sourceAvailable inputAvailable available
      (SignalSource.instanceOutput child output))
    (rule : (childContracts child).RuleName)
    (called : Layer.RuleOccurrence.mk child rule ∈ available)
    (written : output ∈
      (Layer.RuleOccurrence.mk child rule : RuleOccurrence body childContracts).writes) :
    values.sourceValue inputs (SignalSource.instanceOutput child output) isAvailable =
      values.get ⟨child, rule⟩ called output := by
  let selectedRule := Classical.choose isAvailable
  have selectedFacts := Classical.choose_spec isAvailable
  exact values.get_output_eq_of_both_write child selectedFacts.1 called output
    selectedFacts.2 written

theorem childOutputs_eq_get_of_write
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {available : Availability body childContracts} (values : available.Values)
    (covers : CoversAllRules body childContracts available)
    (child : body.context.instancePorts.Name)
    (rule : (childContracts child).RuleName)
    (called : Layer.RuleOccurrence.mk child rule ∈ available)
    (output : (body.context.instancePorts.ports child).outputs.Label)
    (written : output ∈
      (Layer.RuleOccurrence.mk child rule : RuleOccurrence body childContracts).writes) :
    values.childOutputs covers child output =
      values.get ⟨child, rule⟩ called output := by
  let availableOutput := outputAvailable_of_covers covers child output
  let selectedRule := Classical.choose availableOutput
  have selectedFacts := Classical.choose_spec availableOutput
  exact values.get_output_eq_of_both_write child selectedFacts.1 called output
    selectedFacts.2 written

end Availability.Values

namespace RuleOccurrence

noncomputable def inputValues {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {available : Availability body childContracts}
    (occurrence : RuleOccurrence body childContracts)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (values : available.Values)
    (inputs : body.context.ports.inputs.Values) :
    (body.context.instancePorts.ports occurrence.child).inputs.Values :=
  letI : DecidableEq
      (body.context.instancePorts.ports occurrence.child).inputs.Label :=
    (body.context.instancePorts.ports occurrence.child).inputs.labels.decidableEq
  fun input =>
    if member : input ∈ occurrence.reads then
      values.sourceValue inputs (body.wiring.instanceInput occurrence.child input)
        (readsAvailable input member)
    else
      (body.context.instancePorts.ports occurrence.child).inputs.defaultValues input

theorem inputValues_eq_sourceValue
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {available : Availability body childContracts}
    (occurrence : RuleOccurrence body childContracts)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (values : available.Values) (inputs : body.context.ports.inputs.Values)
    (input : (body.context.instancePorts.ports occurrence.child).inputs.Label)
    (member : input ∈ occurrence.reads) :
    occurrence.inputValues readsAvailable values inputs input =
      values.sourceValue inputs (body.wiring.instanceInput occurrence.child input)
        (readsAvailable input member) := by
  unfold inputValues
  split
  · rfl
  · rename_i absent
    exact False.elim (absent member)

/-- Apply one child contract rule using only the inputs certified available at
this point in the schedule. Unread child inputs receive defaults and cannot
affect the selected rule target. -/
noncomputable def evaluate {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {available : Availability body childContracts}
    (occurrence : RuleOccurrence body childContracts)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (values : available.Values)
    (inputs : body.context.ports.inputs.Values)
    (contractState : (childContracts occurrence.child).state.Values) :
    occurrence.Values :=
  let rule := (childContracts occurrence.child).outputRule occurrence.rule
  rule.writesOutputs.write
    (body.context.instancePorts.ports occurrence.child).outputs.defaultValues
    (rule.target
      (rule.readsInputs.project
        (occurrence.inputValues readsAvailable values inputs)) contractState)

theorem evaluate_holds {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {available : Availability body childContracts}
    (occurrence : RuleOccurrence body childContracts)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (values : available.Values)
    (inputs : body.context.ports.inputs.Values)
    (contractState : (childContracts occurrence.child).state.Values) :
    ((childContracts occurrence.child).outputRule occurrence.rule).Holds
      (occurrence.inputValues readsAvailable values inputs) contractState
      (RuleOccurrence.evaluate occurrence readsAvailable values inputs contractState) := by
  unfold CycleOutputRule.Holds evaluate
  exact SignalGroup.write_matches _ _ _
    ((childContracts occurrence.child).rule_writes_nodup occurrence.rule)

end RuleOccurrence

namespace Schedule

theorem initial_mem_final
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable Finish initial)
    (occurrence : RuleOccurrence body childContracts) (member : occurrence ∈ initial) :
    occurrence ∈ schedule.finalAvailability := by
  induction schedule with
  | done finished => exact member
  | call called reads fresh rest induction =>
      exact induction (List.mem_cons_of_mem called member)

/-- Execute the public child-rule calls recorded by a schedule. The result is
indexed by the schedule's final availability, so every later lookup carries
evidence that the producing call occurred. -/
noncomputable def evaluateRules
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable Finish initial)
    (inputs : body.context.ports.inputs.Values)
    (contractState : (child : body.context.instancePorts.Name) →
      (childContracts child).state.Values)
    (initialValues : initial.Values) : schedule.finalAvailability.Values :=
  match schedule with
  | .done _ => initialValues
  | .call occurrence readsAvailable _ rest =>
      Schedule.evaluateRules rest inputs contractState
        (.cons (RuleOccurrence.evaluate occurrence readsAvailable initialValues inputs
          (contractState occurrence.child)) initialValues)

theorem evaluateRules_get_initial
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable Finish initial)
    (inputs : body.context.ports.inputs.Values)
    (contractState : (child : body.context.instancePorts.Name) →
      (childContracts child).state.Values)
    (initialValues : initial.Values)
    (occurrence : RuleOccurrence body childContracts) (member : occurrence ∈ initial) :
    (Schedule.evaluateRules schedule inputs contractState initialValues).get occurrence
        (Schedule.initial_mem_final schedule occurrence member) =
      initialValues.get occurrence member := by
  induction schedule with
  | done finished => rfl
  | @call available called readsAvailable fresh rest induction =>
      let extended : Availability.Values (called :: available) :=
        (DependentList.cons (RuleOccurrence.evaluate called readsAvailable initialValues inputs
          (contractState called.child)) initialValues)
      have throughRest := induction extended
        (List.mem_cons_of_mem called member)
      have different : occurrence ≠ called := by
        intro equal
        subst occurrence
        exact fresh member
      have throughExtension := Availability.Values.get_cons_of_ne different
        (RuleOccurrence.evaluate called readsAvailable initialValues inputs
          (contractState called.child)) initialValues member
      exact throughRest.trans throughExtension

theorem evaluateRules_sourceValue_initial
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable Finish initial)
    (inputs : body.context.ports.inputs.Values)
    (contractState : (child : body.context.instancePorts.Name) →
      (childContracts child).state.Values)
    (initialValues : initial.Values)
    (source : SignalSource body.context.ports body.context.instancePorts signalType)
    (isAvailable : sourceAvailable inputAvailable initial source) :
    initialValues.sourceValue inputs source isAvailable =
      (Schedule.evaluateRules schedule inputs contractState initialValues).sourceValue inputs source
        (sourceAvailable_mono (fun _ available => available)
          (fun occurrence member => Schedule.initial_mem_final schedule occurrence member)
          isAvailable) := by
  cases source with
  | moduleInput input => rfl
  | instanceOutput child output =>
      let rule := Classical.choose isAvailable
      have facts := Classical.choose_spec isAvailable
      rw [initialValues.sourceValue_instanceOutput_eq inputs child output
        isAvailable rule facts.1 facts.2]
      rw [(Schedule.evaluateRules schedule inputs contractState initialValues)
        |>.sourceValue_instanceOutput_eq inputs child output _ rule
          (Schedule.initial_mem_final schedule ⟨child, rule⟩ facts.1) facts.2]
      exact congrFun
        (Schedule.evaluateRules_get_initial schedule inputs contractState initialValues
          ⟨child, rule⟩ facts.1).symm output

/-- Every rule newly called by a schedule holds against the final child-input
and child-output environment produced by the complete schedule. -/
theorem evaluateRules_new_rule_holds
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    {initial : Availability body childContracts}
    (schedule : Schedule body childContracts inputAvailable Finish initial)
    (inputs : body.context.ports.inputs.Values)
    (contractState : (child : body.context.instancePorts.Name) →
      (childContracts child).state.Values)
    (initialValues : initial.Values)
    (covers : CoversAllRules body childContracts schedule.finalAvailability)
    (occurrence : RuleOccurrence body childContracts)
    (member : occurrence ∈ schedule.finalAvailability)
    (new : occurrence ∉ initial) :
    let finalValues := Schedule.evaluateRules schedule inputs contractState initialValues
    ((childContracts occurrence.child).outputRule occurrence.rule).Holds
      (body.wiring.childInputValues inputs (finalValues.childOutputs covers)
        occurrence.child)
      (contractState occurrence.child)
      (finalValues.childOutputs covers occurrence.child) := by
  induction schedule generalizing occurrence with
  | done finished => exact False.elim (new member)
  | @call available called readsAvailable fresh rest induction =>
      let calledValues := RuleOccurrence.evaluate called readsAvailable initialValues inputs
        (contractState called.child)
      let extended : Availability.Values (called :: available) :=
        DependentList.cons calledValues initialValues
      let finalValues := Schedule.evaluateRules rest inputs contractState extended
      have coversRest : CoversAllRules body childContracts rest.finalAvailability := covers
      by_cases equal : occurrence = called
      · subst occurrence
        have immediate := RuleOccurrence.evaluate_holds called readsAvailable initialValues inputs
          (contractState called.child)
        have inputProjection :
            ((childContracts called.child).outputRule called.rule).readsInputs.project
                (RuleOccurrence.inputValues called readsAvailable initialValues inputs) =
              ((childContracts called.child).outputRule called.rule).readsInputs.project
                (body.wiring.childInputValues inputs
                  (finalValues.childOutputs coversRest) called.child) := by
          apply SignalGroup.project_eq_of_eq_on
          intro input inputMem
          have sourceAtFinal :=
            Schedule.evaluateRules_sourceValue_initial
              (Layer.Schedule.call called readsAvailable fresh rest)
              inputs contractState initialValues
              (body.wiring.instanceInput called.child input)
              (readsAvailable input inputMem)
          have sourceIsFinal := finalValues.sourceValue_eq_childOutputs coversRest inputs
            (body.wiring.instanceInput called.child input)
            (sourceAvailable_mono (fun _ available => available)
              (fun previous previousMem =>
                Schedule.initial_mem_final
                  (Layer.Schedule.call called readsAvailable fresh rest)
                  previous previousMem)
              (readsAvailable input inputMem))
          rw [RuleOccurrence.inputValues_eq_sourceValue called readsAvailable initialValues inputs
            input inputMem]
          exact sourceAtFinal.trans sourceIsFinal
        unfold CycleOutputRule.Holds at immediate ⊢
        change
          ((childContracts called.child).outputRule called.rule).writesOutputs.Matches
            (finalValues.childOutputs coversRest called.child)
            (((childContracts called.child).outputRule called.rule).target
              (((childContracts called.child).outputRule called.rule).readsInputs.project
                (body.wiring.childInputValues inputs
                  (finalValues.childOutputs coversRest) called.child))
              (contractState called.child))
        rw [← inputProjection]
        apply SignalGroup.Matches.of_eq_on _ immediate
        intro output outputMem
        have preserved := Schedule.evaluateRules_get_initial rest inputs contractState extended
          called (List.Mem.head available)
        have finalOutput := finalValues.childOutputs_eq_get_of_write coversRest
          called.child called.rule
          (Schedule.initial_mem_final rest called (List.Mem.head available)) output outputMem
        have headValue := Availability.Values.get_cons_self called calledValues
          initialValues (List.Mem.head available)
        exact (congrFun headValue.symm output).trans
          ((congrFun preserved.symm output).trans finalOutput.symm)
      · apply induction extended coversRest occurrence member
        intro inExtended
        rcases List.mem_cons.mp inExtended with isCalled | wasInitial
        · exact equal isCalled
        · exact new wasInitial

theorem evaluateRules_outputRulesHold
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    (schedule : Schedule body childContracts inputAvailable Finish [])
    (inputs : body.context.ports.inputs.Values)
    (contractState : (child : body.context.instancePorts.Name) →
      (childContracts child).state.Values)
    (covers : CoversAllRules body childContracts schedule.finalAvailability) :
    let finalValues := Schedule.evaluateRules schedule inputs contractState .nil
    ∀ child,
      (childContracts child).OutputRulesHold
        (body.wiring.childInputValues inputs (finalValues.childOutputs covers) child)
        (contractState child) (finalValues.childOutputs covers child) := by
  dsimp only
  intro child rule
  exact Schedule.evaluateRules_new_rule_holds schedule inputs contractState .nil covers
    ⟨child, rule⟩ (covers child rule) (by intro impossible; cases impossible)

/-- A complete scheduled order of public child rules constructs a structural
solution for every root input and structural state. Together with
`Schedule.hasAtMostOneSolution`, this makes the schedule positive evidence of
both acyclicity and evaluability without defining structural meaning by order. -/
theorem hasSolution
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    (children : ChildStructures body childContracts)
    {inputAvailable : body.context.ports.inputs.Label → Prop}
    {Finish : Availability body childContracts → Prop}
    (schedule : Schedule body childContracts inputAvailable Finish [])
    (covers : CoversAllRules body childContracts schedule.finalAvailability) :
    (moduleStructure body children).HasSolution := by
  intro inputs structuralState
  let StateProperty := fun child contractState =>
    (children child).certification.stateCorresponds contractState (structuralState child)
  have stateAvailable : ∀ child, ∃ contractState, StateProperty child contractState :=
    fun child => (children child).certification.hasCorrespondingState (structuralState child)
  rcases body.context.instancePorts.names.exists_pi StateProperty stateAvailable with
    ⟨contractState, stateCorresponds⟩
  let finalValues := Schedule.evaluateRules schedule inputs contractState .nil
  let childOutputValues := finalValues.childOutputs covers
  have rulesHold := Schedule.evaluateRules_outputRulesHold schedule inputs contractState covers
  let ProposalProperty := fun child proposal =>
    (children child).moduleStructure.IsSolution
      (body.wiring.childInputValues inputs childOutputValues child)
      (structuralState child) proposal
  have proposalsAvailable : ∀ child, ∃ proposal, ProposalProperty child proposal :=
    fun child => (children child).certification.hasStructuralResult
      (body.wiring.childInputValues inputs childOutputValues child)
      (structuralState child)
  rcases body.context.instancePorts.names.exists_pi ProposalProperty
      proposalsAvailable with ⟨childProposals, childrenSatisfy⟩
  have childOutputsEqual : ∀ child,
      (childProposals child).outputs = childOutputValues child := by
    intro child
    rcases (children child).certification.implements
        (body.wiring.childInputValues inputs childOutputValues child)
        (contractState child) (structuralState child) (childProposals child)
        (stateCorresponds child) (childrenSatisfy child) with
      ⟨nextContractState, evaluates, nextCorresponds⟩
    exact (childContracts child).outputs_unique
      (body.wiring.childInputValues inputs childOutputValues child)
      (contractState child) (childProposals child).outputs
      (childOutputValues child) evaluates.1 (rulesHold child)
  have outputFamiliesEqual :
      (fun child => (childProposals child).outputs) = childOutputValues := by
    funext child
    exact childOutputsEqual child
  have childInputsEqual : ∀ child,
      ProposedValues.childInputs body ((fun name => (children name).moduleStructure)) inputs
          childProposals child =
        body.wiring.childInputValues inputs childOutputValues child := by
    intro child
    unfold ProposedValues.childInputs
    rw [outputFamiliesEqual]
  refine ⟨ProposedValues.compositeFromChildren body ((fun name => (children name).moduleStructure))
    inputs childProposals, ProposedValues.compositeFromChildren_isSolution
      body ((fun name => (children name).moduleStructure)) inputs structuralState childProposals ?_⟩
  intro child
  rw [childInputsEqual child]
  exact childrenSatisfy child

end Schedule

namespace RuleSchedules

/-- Parent output and state schedules, once shown to cover every immediate
child rule, provide structural existence as well as uniqueness. -/
theorem hasSolution
    {body : ModuleBody} {childContracts : ChildCycleContracts body}
    {contract : ModuleCycleContract body.context.ports}
    (schedules : RuleSchedules body childContracts contract)
    (covers : schedules.CoversChildren)
    (children : ChildStructures body childContracts) :
    (moduleStructure body children).HasSolution :=
  schedules.combined.schedule.hasSolution children (by
    intro child rule
    rcases covers child rule with stateMember | ⟨parentRule, outputMember⟩
    · exact Combined.add_includes schedules.combineOutputs schedules.state
        (by intro input _; trivial) _ stateMember
    · exact Combined.add_preserves schedules.combineOutputs schedules.state
        (by intro input _; trivial) _
        (mem_combineOutputs schedules parentRule _ outputMember))

end RuleSchedules

end Silean.Contracts.Cycle.Certification.Layer
