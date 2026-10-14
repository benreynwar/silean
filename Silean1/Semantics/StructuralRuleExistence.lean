import Silean.Semantics.StructuralRuleSemantics

namespace Silean.ModuleStructuralCertification.Layer

open Silean

/-! # Existence from structural rule schedules

The evaluator below is used only to prove existence. It chooses witnesses from
the children's structural certifications while following a checked dependency
schedule. Neither the evaluator nor its choices become part of the hardware's
semantics or stored certification. -/

/-- A scheduled occurrence stores one complete solution witness for its child.
Only the outputs named by that occurrence's rule are subsequently observed. -/
abbrev RuleOccurrence.Values
    (children : ChildStructures body childRules)
    (occurrence : RuleOccurrence body childRules) :=
  HierStep ((children occurrence.child).moduleStructure)

/-- Witnesses corresponding position-for-position to scheduled occurrences. -/
abbrev Availability.Values
    (children : ChildStructures body childRules)
    (available : Availability body childRules) :=
  DependentList (RuleOccurrence.Values children) available

namespace Availability.Values

noncomputable def get
    {children : ChildStructures body childRules}
    {available : Availability body childRules}
    (values : Availability.Values children available)
    (occurrence : RuleOccurrence body childRules)
    (member : occurrence ∈ available) : occurrence.Values children := by
  letI : DecidableEq (RuleOccurrence body childRules) := inferInstance
  exact DependentList.get values (ListIndex.ofMem member)

@[simp] theorem get_cons_self
    {children : ChildStructures body childRules}
    (occurrence : RuleOccurrence body childRules)
    (value : occurrence.Values children)
    {available : Availability body childRules}
    (values : Availability.Values children available)
    (member : occurrence ∈ occurrence :: available) :
    get (.cons value values) occurrence member = value := by
  unfold get
  simp only [ListIndex.ofMem_cons_self]
  rfl

theorem get_cons_of_ne
    {children : ChildStructures body childRules}
    {occurrence head : RuleOccurrence body childRules}
    (different : occurrence ≠ head) (value : head.Values children)
    {available : Availability body childRules}
    (values : Availability.Values children available)
    (member : occurrence ∈ available) :
    get (.cons value values) occurrence (List.mem_cons_of_mem head member) =
      get values occurrence member := by
  letI : DecidableEq (RuleOccurrence body childRules) := inferInstance
  unfold get
  rw [ListIndex.ofMem_cons_of_ne different]
  simp only [DependentList.get]
  exact member

theorem get_eq_of_both_write
    {children : ChildStructures body childRules}
    {available : Availability body childRules}
    (values : Availability.Values children available)
    (child : body.instancePorts.Name)
    {left right : (childRules child).RuleName}
    (leftMem : RuleOccurrence.mk child left ∈ available)
    (rightMem : RuleOccurrence.mk child right ∈ available)
    (output : (body.instancePorts.ports child).outputs.Label)
    (leftWrites : output ∈
      (RuleOccurrence.mk child left : RuleOccurrence body childRules).writes)
    (rightWrites : output ∈
      (RuleOccurrence.mk child right : RuleOccurrence body childRules).writes) :
    values.get ⟨child, left⟩ leftMem =
      values.get ⟨child, right⟩ rightMem := by
  have equal := (childRules child).rule_eq_of_both_write leftWrites rightWrites
  change left = right at equal
  subst right
  rfl

/-- Read one total output map per child after all structural rules are covered.
Exact rule coverage makes the selected producer canonical. -/
noncomputable def childOutputs
    {children : ChildStructures body childRules}
    {available : Availability body childRules}
    (values : Availability.Values children available)
    (covers : CoversAllRules body childRules available) :
    (child : body.instancePorts.Name) →
      (body.instancePorts.ports child).outputs.Values :=
  fun child output =>
    let availableOutput := outputAvailable_of_covers covers child output
    let rule := Classical.choose availableOutput
    let facts := Classical.choose_spec availableOutput
    (values.get ⟨child, rule⟩ facts.1).outputs output

/-- Read a source whose producer has already been scheduled. -/
noncomputable def sourceValue
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childRules}
    (values : Availability.Values children available)
    (inputs : body.ports.inputs.Values)
    (source : SignalSource body.ports body.instancePorts signalType)
    (isAvailable : sourceAvailable inputAvailable available source) :
    signalType.Denote := by
  cases source with
  | moduleInput input => exact inputs input
  | instanceOutput child output =>
      let rule := Classical.choose isAvailable
      have facts := Classical.choose_spec isAvailable
      exact (values.get ⟨child, rule⟩ facts.1).outputs output

theorem sourceValue_eq_childOutputs
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childRules}
    (values : Availability.Values children available)
    (covers : CoversAllRules body childRules available)
    (inputs : body.ports.inputs.Values)
    (source : SignalSource body.ports body.instancePorts signalType)
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
      have ruleEqual : leftRule = rightRule :=
        (childRules child).rule_eq_of_both_write leftFacts.2 rightFacts.2
      subst rightRule
      rfl

theorem sourceValue_instanceOutput_eq
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childRules}
    (values : Availability.Values children available)
    (inputs : body.ports.inputs.Values)
    (child : body.instancePorts.Name)
    (output : (body.instancePorts.ports child).outputs.Label)
    (isAvailable : sourceAvailable inputAvailable available
      (SignalSource.instanceOutput child output))
    (rule : (childRules child).RuleName)
    (called : RuleOccurrence.mk child rule ∈ available)
    (written : output ∈
      (RuleOccurrence.mk child rule : RuleOccurrence body childRules).writes) :
    values.sourceValue inputs (SignalSource.instanceOutput child output) isAvailable =
      (values.get ⟨child, rule⟩ called).outputs output := by
  let selectedRule := Classical.choose isAvailable
  have selectedFacts := Classical.choose_spec isAvailable
  exact congrFun (congrArg HierStep.outputs
    (values.get_eq_of_both_write child selectedFacts.1 called output
      selectedFacts.2 written)) output

theorem childOutputs_eq_get_of_write
    {children : ChildStructures body childRules}
    {available : Availability body childRules}
    (values : Availability.Values children available)
    (covers : CoversAllRules body childRules available)
    (child : body.instancePorts.Name)
    (rule : (childRules child).RuleName)
    (called : RuleOccurrence.mk child rule ∈ available)
    (output : (body.instancePorts.ports child).outputs.Label)
    (written : output ∈
      (RuleOccurrence.mk child rule : RuleOccurrence body childRules).writes) :
    values.childOutputs covers child output =
      (values.get ⟨child, rule⟩ called).outputs output := by
  let availableOutput := outputAvailable_of_covers covers child output
  let selectedRule := Classical.choose availableOutput
  have selectedFacts := Classical.choose_spec availableOutput
  exact congrFun (congrArg HierStep.outputs
    (values.get_eq_of_both_write child selectedFacts.1 called output
      selectedFacts.2 written)) output

end Availability.Values

namespace RuleOccurrence

/-- Complete child inputs for a proof-local rule evaluation. Unread inputs use
defaults; the certified dependency theorem ensures they cannot affect the
outputs written by this rule. -/
noncomputable def inputValues
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childRules}
    (occurrence : RuleOccurrence body childRules)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (values : Availability.Values children available)
    (inputs : body.ports.inputs.Values) :
    (body.instancePorts.ports occurrence.child).inputs.Values :=
  letI : DecidableEq
      (body.instancePorts.ports occurrence.child).inputs.Label :=
    (body.instancePorts.ports occurrence.child).inputs.labels.decidableEq
  fun input =>
    if member : input ∈ occurrence.reads then
      values.sourceValue inputs (body.wiring.instanceInput occurrence.child input)
        (readsAvailable input member)
    else
      (body.instancePorts.ports occurrence.child).inputs.defaultValues input

theorem inputValues_eq_sourceValue
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childRules}
    (occurrence : RuleOccurrence body childRules)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (values : Availability.Values children available)
    (inputs : body.ports.inputs.Values)
    (input : (body.instancePorts.ports occurrence.child).inputs.Label)
    (member : input ∈ occurrence.reads) :
    occurrence.inputValues readsAvailable values inputs input =
      values.sourceValue inputs (body.wiring.instanceInput occurrence.child input)
        (readsAvailable input member) := by
  unfold inputValues
  split
  · rfl
  · rename_i absent
    exact False.elim (absent member)

/-- Choose one solution for the partial rule inputs. -/
noncomputable def evaluate
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childRules}
    (occurrence : RuleOccurrence body childRules)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (values : Availability.Values children available)
    (inputs : body.ports.inputs.Values)
    (currentState : (child : body.instancePorts.Name) →
      (children child).moduleStructure.State) : occurrence.Values children :=
  Classical.choose <|
    (children occurrence.child).certification.structural.hasSolution
      (occurrence.inputValues readsAvailable values inputs)
      (currentState occurrence.child)

theorem evaluate_isSolution
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childRules}
    (occurrence : RuleOccurrence body childRules)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (values : Availability.Values children available)
    (inputs : body.ports.inputs.Values)
    (currentState : (child : body.instancePorts.Name) →
      (children child).moduleStructure.State) :
    (children occurrence.child).moduleStructure.IsSolution
      (occurrence.evaluate readsAvailable values inputs currentState) :=
  (Classical.choose_spec <|
    (children occurrence.child).certification.structural.hasSolution
      (occurrence.inputValues readsAvailable values inputs)
      (currentState occurrence.child)).1

theorem evaluate_inputs
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childRules}
    (occurrence : RuleOccurrence body childRules)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (values : Availability.Values children available)
    (inputs : body.ports.inputs.Values)
    (currentState : (child : body.instancePorts.Name) →
      (children child).moduleStructure.State) :
    (occurrence.evaluate readsAvailable values inputs currentState).inputs =
      occurrence.inputValues readsAvailable values inputs :=
  (Classical.choose_spec <|
    (children occurrence.child).certification.structural.hasSolution
      (occurrence.inputValues readsAvailable values inputs)
      (currentState occurrence.child)).2.1

theorem evaluate_currentState
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {available : Availability body childRules}
    (occurrence : RuleOccurrence body childRules)
    (readsAvailable : ∀ input, input ∈ occurrence.reads →
      sourceAvailable inputAvailable available
        (body.wiring.instanceInput occurrence.child input))
    (values : Availability.Values children available)
    (inputs : body.ports.inputs.Values)
    (currentState : (child : body.instancePorts.Name) →
      (children child).moduleStructure.State) :
    HierStep.currentState (children occurrence.child).moduleStructure
        (occurrence.evaluate readsAvailable values inputs currentState) =
      currentState occurrence.child :=
  (Classical.choose_spec <|
    (children occurrence.child).certification.structural.hasSolution
      (occurrence.inputValues readsAvailable values inputs)
      (currentState occurrence.child)).2.2

end RuleOccurrence

namespace Schedule

noncomputable def evaluateRules
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (schedule : Schedule body childRules inputAvailable Finish initial)
    (inputs : body.ports.inputs.Values)
    (currentState : (child : body.instancePorts.Name) →
      (children child).moduleStructure.State)
    (initialValues : Availability.Values children initial) :
    Availability.Values children schedule.finalAvailability :=
  match schedule with
  | .done _ => initialValues
  | .call occurrence readsAvailable _ rest =>
      evaluateRules rest inputs currentState
        (.cons (occurrence.evaluate readsAvailable initialValues inputs currentState)
          initialValues)

theorem evaluateRules_get_initial
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (schedule : Schedule body childRules inputAvailable Finish initial)
    (inputs : body.ports.inputs.Values)
    (currentState : (child : body.instancePorts.Name) →
      (children child).moduleStructure.State)
    (initialValues : Availability.Values children initial)
    (occurrence : RuleOccurrence body childRules) (member : occurrence ∈ initial) :
    (schedule.evaluateRules inputs currentState initialValues).get occurrence
        (schedule.initial_mem_final occurrence member) =
      initialValues.get occurrence member := by
  induction schedule with
  | done finished => rfl
  | @call available called readsAvailable fresh rest induction =>
      let calledValue := called.evaluate readsAvailable initialValues inputs currentState
      let extended : Availability.Values children (called :: available) :=
        .cons calledValue initialValues
      have throughRest := induction extended (List.mem_cons_of_mem called member)
      have different : occurrence ≠ called := by
        intro equal
        subst occurrence
        exact fresh member
      have throughExtension := Availability.Values.get_cons_of_ne different
        calledValue initialValues member
      exact throughRest.trans throughExtension

theorem evaluateRules_sourceValue_initial
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (schedule : Schedule body childRules inputAvailable Finish initial)
    (inputs : body.ports.inputs.Values)
    (currentState : (child : body.instancePorts.Name) →
      (children child).moduleStructure.State)
    (initialValues : Availability.Values children initial)
    (source : SignalSource body.ports body.instancePorts signalType)
    (isAvailable : sourceAvailable inputAvailable initial source) :
    initialValues.sourceValue inputs source isAvailable =
      (schedule.evaluateRules inputs currentState initialValues).sourceValue inputs source
        (sourceAvailable_mono (fun _ available => available)
          (fun occurrence member => schedule.initial_mem_final occurrence member)
          isAvailable) := by
  cases source with
  | moduleInput input => rfl
  | instanceOutput child output =>
      let rule := Classical.choose isAvailable
      have facts := Classical.choose_spec isAvailable
      rw [initialValues.sourceValue_instanceOutput_eq inputs child output
        isAvailable rule facts.1 facts.2]
      rw [(schedule.evaluateRules inputs currentState initialValues)
        |>.sourceValue_instanceOutput_eq inputs child output _ rule
          (schedule.initial_mem_final ⟨child, rule⟩ facts.1) facts.2]
      have stepEqual := schedule.evaluateRules_get_initial inputs currentState
        initialValues ⟨child, rule⟩ facts.1
      exact congrFun (congrArg HierStep.outputs stepEqual.symm) output

/-- Every newly scheduled occurrence is represented by a genuine child
solution whose declared reads agree with the final wiring environment. -/
theorem evaluateRules_new_rule
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (schedule : Schedule body childRules inputAvailable Finish initial)
    (inputs : body.ports.inputs.Values)
    (currentState : (child : body.instancePorts.Name) →
      (children child).moduleStructure.State)
    (initialValues : Availability.Values children initial)
    (covers : CoversAllRules body childRules schedule.finalAvailability)
    (occurrence : RuleOccurrence body childRules)
    (member : occurrence ∈ schedule.finalAvailability)
    (new : occurrence ∉ initial) :
    let finalValues := schedule.evaluateRules inputs currentState initialValues
    let finalStep := finalValues.get occurrence member
    (children occurrence.child).moduleStructure.IsSolution finalStep ∧
      InputsAgreeOn occurrence.reads finalStep.inputs
        (body.wiring.childInputValues inputs
          (finalValues.childOutputs covers) occurrence.child) ∧
      HierStep.currentState (children occurrence.child).moduleStructure
          finalStep = currentState occurrence.child := by
  induction schedule generalizing occurrence with
  | done finished => exact False.elim (new member)
  | @call available called readsAvailable fresh rest induction =>
      let calledValue := called.evaluate readsAvailable initialValues inputs currentState
      let extended : Availability.Values children (called :: available) :=
        .cons calledValue initialValues
      let finalValues := rest.evaluateRules inputs currentState extended
      have coversRest : CoversAllRules body childRules rest.finalAvailability := covers
      by_cases equal : occurrence = called
      · subst occurrence
        have preserved := rest.evaluateRules_get_initial inputs currentState
          extended called (List.Mem.head available)
        have headValue := Availability.Values.get_cons_self called calledValue
          initialValues (List.Mem.head available)
        have finalStepEqual : finalValues.get called member = calledValue := by
          exact preserved.trans headValue
        have immediateSolution := called.evaluate_isSolution readsAvailable
          initialValues inputs currentState
        have immediateInputs := called.evaluate_inputs readsAvailable
          initialValues inputs currentState
        have immediateState := called.evaluate_currentState readsAvailable
          initialValues inputs currentState
        change (children called.child).moduleStructure.IsSolution
            (finalValues.get called member) ∧
          InputsAgreeOn called.reads (finalValues.get called member).inputs
            (body.wiring.childInputValues inputs
              (finalValues.childOutputs coversRest) called.child) ∧
          HierStep.currentState (children called.child).moduleStructure
              (finalValues.get called member) = currentState called.child
        rw [finalStepEqual]
        refine ⟨immediateSolution, ?_, immediateState⟩
        intro input inputMem
        rw [immediateInputs]
        rw [called.inputValues_eq_sourceValue readsAvailable initialValues inputs
          input inputMem]
        have sourceAtFinal := evaluateRules_sourceValue_initial
          (Schedule.call called readsAvailable fresh rest) inputs currentState
          initialValues (body.wiring.instanceInput called.child input)
          (readsAvailable input inputMem)
        have sourceIsFinal := finalValues.sourceValue_eq_childOutputs coversRest
          inputs (body.wiring.instanceInput called.child input)
          (sourceAvailable_mono (fun _ available => available)
            (fun previous previousMem =>
              (Schedule.call called readsAvailable fresh rest).initial_mem_final
                previous previousMem)
            (readsAvailable input inputMem))
        exact sourceAtFinal.trans sourceIsFinal
      · apply induction extended coversRest occurrence member
        intro inExtended
        rcases List.mem_cons.mp inExtended with isCalled | wasInitial
        · exact equal isCalled
        · exact new wasInitial

end Schedule

/-- A complete structural-rule schedule constructs a solution for every root
input and composite state using no behavioral contract. -/
theorem Schedule.hasSolution
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    (schedule : Schedule body childRules inputAvailable Finish [])
    (children : ChildStructures body childRules)
    (covers : CoversAllRules body childRules schedule.finalAvailability) :
    (moduleStructure body children).HasSolution := by
  intro inputs currentState
  let finalValues := schedule.evaluateRules inputs currentState .nil
  let scheduledOutputs := finalValues.childOutputs covers
  let ChildProperty := fun child hierStep =>
    (children child).moduleStructure.IsSolution hierStep ∧
      hierStep.inputs =
        body.wiring.childInputValues inputs scheduledOutputs child ∧
      HierStep.currentState (children child).moduleStructure hierStep =
        currentState child
  have childrenAvailable : ∀ child, ∃ hierStep, ChildProperty child hierStep :=
    fun child => (children child).certification.structural.hasSolution
      (body.wiring.childInputValues inputs scheduledOutputs child)
      (currentState child)
  rcases body.instancePorts.names.exists_pi ChildProperty childrenAvailable with
    ⟨childHierSteps, childProperties⟩
  have childOutputsEqual : ∀ child,
      (childHierSteps child).outputs = scheduledOutputs child := by
    intro child
    funext output
    let availableOutput := outputAvailable_of_covers covers child output
    let rule := Classical.choose availableOutput
    have facts := Classical.choose_spec availableOutput
    let occurrence : RuleOccurrence body childRules := ⟨child, rule⟩
    let scheduledStep := finalValues.get occurrence facts.1
    have scheduledProperties := schedule.evaluateRules_new_rule inputs currentState
      .nil covers occurrence facts.1 (by intro impossible; cases impossible)
    have readInputsAgree : InputsAgreeOn occurrence.reads scheduledStep.inputs
        (childHierSteps child).inputs := by
      intro input inputMem
      exact scheduledProperties.2.1 input inputMem |>.trans
        (congrFun (childProperties child).2.1.symm input)
    have statesEqual :
        HierStep.currentState (children child).moduleStructure scheduledStep =
          HierStep.currentState (children child).moduleStructure
            (childHierSteps child) :=
      scheduledProperties.2.2.trans (childProperties child).2.2.symm
    have determined := (children child).certification.determines rule
      scheduledStep (childHierSteps child) scheduledProperties.1
      (childProperties child).1 statesEqual readInputsAgree output facts.2
    have scheduledOutput := finalValues.childOutputs_eq_get_of_write covers
      child rule facts.1 output facts.2
    exact determined.symm.trans scheduledOutput.symm
  have outputFamiliesEqual :
      (fun child => (childHierSteps child).outputs) = scheduledOutputs := by
    funext child
    exact childOutputsEqual child
  have childInputsSatisfy : HierStep.ChildInputsSatisfy body inputs
      (fun child => (childHierSteps child).inputs)
      (fun child => (childHierSteps child).outputs) := by
    intro child
    change (childHierSteps child).inputs =
      body.wiring.childInputValues inputs
        (fun child => (childHierSteps child).outputs) child
    rw [(childProperties child).2.1, outputFamiliesEqual]
  let hierStep := HierStep.compositeFromChildren body
    (fun child => (children child).moduleStructure) inputs childHierSteps
  refine ⟨hierStep,
    HierStep.compositeFromChildren_isSolution body
      (fun child => (children child).moduleStructure) inputs childHierSteps
      childInputsSatisfy (fun child => (childProperties child).1), rfl, ?_⟩
  funext child
  exact (childProperties child).2.2

/-- Package the two generic schedule consequences as one contract-independent
structural certification. -/
theorem Schedule.certification
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    (schedule : Schedule body childRules inputAvailable Finish [])
    (children : ChildStructures body childRules)
    (allInputsAvailable : ∀ input, inputAvailable input)
    (covers : CoversAllRules body childRules schedule.finalAvailability) :
    ModuleStructuralCertification (moduleStructure body children) where
  hasSolution := schedule.hasSolution children covers
  hasAtMostOneSolution := schedule.hasAtMostOneSolution children
    allInputsAvailable covers

end Silean.ModuleStructuralCertification.Layer
