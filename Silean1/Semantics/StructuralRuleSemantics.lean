import Silean.Semantics.StructuralRuleSchedule

namespace Silean.ModuleStructuralCertification.Layer

open Silean

/-! # Semantic consequences of structural rule schedules -/

def ChildOutputsAgree
    {children : ChildStructures body childRules}
    (available : Availability body childRules)
    (left right : HierStep (moduleStructure body children)) : Prop :=
  ∀ occurrence, occurrence ∈ available →
    ∀ output, output ∈ occurrence.writes →
      (left.children occurrence.child).outputs output =
        (right.children occurrence.child).outputs output

theorem sourceValue_eq_of_available
    {children : ChildStructures body childRules}
    {available : Availability body childRules}
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
    {children : ChildStructures body childRules}
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    {initial : Availability body childRules}
    (schedule : Schedule body childRules inputAvailable Finish initial)
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
        exact (children occurrence.child).certification.determines occurrence.rule
          _ _ (leftSatisfies.2.2 occurrence.child)
          (rightSatisfies.2.2 occurrence.child)
          (congrFun currentStatesEqual occurrence.child) childInputsAgree
      have extended : ChildOutputsAgree (occurrence :: available) left right := by
        intro called member output outputMem
        rcases List.mem_cons.mp member with equal | previous
        · cases equal
          exact writesAgree output outputMem
        · exact initialAgreement called previous output outputMem
      exact induction extended

structure ReplayResult
    (inputAvailable : body.ports.inputs.Label → Prop)
    (initial : Availability body childRules)
    (sourceFinal : Availability body childRules)
    (SourceFinish : Availability body childRules → Prop) where
  final : Availability body childRules
  schedule : Schedule body childRules inputAvailable (fun _ => True) initial
  final_eq : schedule.finalAvailability = final
  covered : ∀ occurrence, occurrence ∈ initial → occurrence ∈ final
  sourceFinished : SourceFinish sourceFinal
  sourceCovered : ∀ occurrence, occurrence ∈ sourceFinal → occurrence ∈ final

/-- Replay a schedule after another call sequence, omitting rules already
available in the target. -/
noncomputable def replay
    {sourceInputs targetInputs : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    {sourceInitial targetInitial : Availability body childRules}
    (schedule : Schedule body childRules sourceInputs Finish sourceInitial)
    (inputsMono : ∀ input, sourceInputs input → targetInputs input)
    (initialCovered : ∀ occurrence, occurrence ∈ sourceInitial →
      occurrence ∈ targetInitial) :
    ReplayResult targetInputs targetInitial schedule.finalAvailability Finish := by
  letI : DecidableEq (RuleOccurrence body childRules) := inferInstance
  induction schedule generalizing targetInitial with
  | done finished =>
      exact ⟨targetInitial, .done trivial, rfl,
        (by intro occurrence member; exact member),
        finished, initialCovered⟩
  | @call sourceAvailable occurrence readsAvailable fresh rest induction =>
      if already : occurrence ∈ targetInitial then
        apply induction (targetInitial := targetInitial)
        intro previous member
        rcases List.mem_cons.mp member with equal | old
        · cases equal
          exact already
        · exact initialCovered previous old
      else
        let replayed := induction (targetInitial := occurrence :: targetInitial)
          (fun previous member => by
            rcases List.mem_cons.mp member with equal | old
            · exact List.mem_cons.mpr (Or.inl equal)
            · exact List.mem_cons.mpr (Or.inr (initialCovered previous old)))
        refine ⟨replayed.final, .call occurrence ?_ already replayed.schedule,
          ?_, ?_, replayed.sourceFinished, replayed.sourceCovered⟩
        · intro input inputMem
          exact sourceAvailable_mono inputsMono initialCovered
            (readsAvailable input inputMem)
        · exact replayed.final_eq
        · intro previous member
          exact replayed.covered previous
            (List.mem_cons_of_mem occurrence member)

end Schedule

/-- A complete structural-rule schedule proves uniqueness of the composite's
simultaneous equations without reference to any behavioral contract. -/
theorem Schedule.hasAtMostOneSolution
    {inputAvailable : body.ports.inputs.Label → Prop}
    {Finish : Availability body childRules → Prop}
    (schedule : Schedule body childRules inputAvailable Finish [])
    (children : ChildStructures body childRules)
    (allInputsAvailable : ∀ input, inputAvailable input)
    (covers : CoversAllRules body childRules schedule.finalAvailability) :
    (moduleStructure body children).HasAtMostOneSolution := by
  intro left right leftSatisfies rightSatisfies inputsEqual currentStatesEqual
  have childOutputsAgree := schedule.finishAgreement left right
    (fun input _ => congrFun inputsEqual input) leftSatisfies rightSatisfies
    currentStatesEqual (by intro occurrence member; cases member)
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
    apply (children name).certification.structural.hasAtMostOneSolution
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

end Silean.ModuleStructuralCertification.Layer
