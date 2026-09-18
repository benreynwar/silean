import Silean.Semantics.StructuralEquations

namespace Silean

/-! # Structural dependencies and complete uniqueness

A `StructuralRule` records which root inputs are sufficient to determine
selected root outputs of any two satisfying hierarchy assignments with the
same current physical state. These are semantic dependency facts, not
evaluation steps stored in `ModuleStructure`.
-/

def InputsAgreeOn {ports : ModulePorts} (reads : List ports.inputs.Label)
    (left right : ports.inputs.Values) : Prop :=
  ∀ input, input ∈ reads → left input = right input

structure StructuralRule {ports : ModulePorts}
    (module : ModuleStructure ports) where
  /-- Boundary inputs on which the selected outputs may depend. -/
  reads : List ports.inputs.Label
  /-- Boundary outputs determined by those inputs and current state. -/
  writes : List ports.outputs.Label
  /-- Any two solutions with equal current state and agreement on `reads`
  agree on `writes`. -/
  determines : ∀ (left right : HierStep module),
    module.IsSolution left →
    module.IsSolution right →
    HierStep.currentState module left = HierStep.currentState module right →
    InputsAgreeOn reads left.inputs right.inputs →
    ∀ output, output ∈ writes → left.outputs output = right.outputs output

/-- Complete uniqueness compares the full hierarchy assignment, including
every internal input, output, and leaf next-state value. Root inputs and
current physical state are the fixed coordinates of the structural problem. -/
def ModuleStructure.HasAtMostOneSolution {ports : ModulePorts}
    (module : ModuleStructure ports) : Prop :=
  ∀ (left right : HierStep module),
    module.IsSolution left →
    module.IsSolution right →
    left.inputs = right.inputs →
    HierStep.currentState module left = HierStep.currentState module right →
    left = right

/-- Every root input and current-state choice has a satisfying complete
hierarchy assignment. -/
def ModuleStructure.HasSolution {ports : ModulePorts}
    (module : ModuleStructure ports) : Prop :=
  ∀ inputs currentState,
    ∃ hierStep, module.IsSolution hierStep ∧
      hierStep.inputs = inputs ∧
      HierStep.currentState module hierStep = currentState

def ModuleStructure.HasExactlyOneSolution {ports : ModulePorts}
    (module : ModuleStructure ports) : Prop :=
  module.HasSolution ∧ module.HasAtMostOneSolution

def Primitive.ruleReads (primitive : Primitive) :
    List primitive.ports.inputs.Label :=
  primitive.outputReads

def Primitive.ruleWrites (primitive : Primitive) :
    List primitive.ports.outputs.Label :=
  primitive.ports.outputs.labels.values

/-- The assignment obtained by evaluating a primitive's defining functions.
This witnesses existence without making evaluation order part of the
structural solution relation. -/
def Primitive.canonicalHierStep (primitive : Primitive)
    (inputs : primitive.ports.inputs.Values)
    (currentState : primitive.localState.Values) :
    HierStep (.primitive primitive) :=
  { inputs := inputs
    currentState := currentState
    outputs := primitive.outputValues inputs currentState
    nextState := primitive.nextStateValues inputs currentState }

@[simp] theorem Primitive.canonicalHierStep_isSolution
    (primitive : Primitive) (inputs : primitive.ports.inputs.Values)
    (currentState : primitive.localState.Values) :
    (ModuleStructure.primitive primitive).IsSolution
      (primitive.canonicalHierStep inputs currentState) :=
  ⟨rfl, rfl⟩

theorem Primitive.hasSolution (primitive : Primitive) :
    (ModuleStructure.primitive primitive).HasSolution := by
  intro inputs currentState
  exact ⟨primitive.canonicalHierStep inputs currentState, by simp, rfl, rfl⟩

def Primitive.structuralRule (primitive : Primitive) :
    StructuralRule (.primitive primitive) where
  reads := primitive.ruleReads
  writes := primitive.ruleWrites
  determines := by
    intro left right leftSatisfies rightSatisfies statesEqual
      inputsAgree output _
    have outputsEqual := primitive.outputRespectsReads
      left.inputs right.inputs left.currentState inputsAgree
    have rightOutput :
        right.outputs = primitive.outputValues right.inputs left.currentState := by
      rw [statesEqual]
      exact rightSatisfies.1
    exact congrFun
      (leftSatisfies.1.trans (outputsEqual.trans rightOutput.symm)) output

@[simp] theorem Primitive.structuralRule_writes (primitive : Primitive) :
    primitive.structuralRule.writes = primitive.ruleWrites :=
  rfl

@[simp] theorem Primitive.structuralRule_reads (primitive : Primitive) :
    primitive.structuralRule.reads = primitive.ruleReads :=
  rfl

theorem Primitive.hasAtMostOneSolution (primitive : Primitive) :
    (ModuleStructure.primitive primitive).HasAtMostOneSolution := by
  intro left right leftSatisfies rightSatisfies inputsEqual statesEqual
  cases left
  cases right
  simp_all only [ModuleStructure.IsSolution, HierStep.inputs,
    HierStep.outputs, HierStep.currentState, HierStep.nextState,
    Primitive.IsSolution, Primitive.OutputsSatisfy,
    Primitive.NextStateSatisfy]

/-- A behavioral blackbox has the same leaf-equation uniqueness as a concrete
primitive; the distinction concerns implementation closure, not semantics. -/
theorem Primitive.blackbox_hasAtMostOneSolution (behavior : Primitive) :
    (ModuleStructure.blackbox behavior).HasAtMostOneSolution := by
  intro left right leftSatisfies rightSatisfies inputsEqual statesEqual
  cases left
  cases right
  simp_all only [ModuleStructure.IsSolution, HierStep.inputs,
    HierStep.outputs, HierStep.currentState, HierStep.nextState,
    Primitive.IsSolution, Primitive.OutputsSatisfy,
    Primitive.NextStateSatisfy]

def Composition.SignalSplitter.structuralRule
    (splitter : Composition.SignalSplitter) :
    StructuralRule (.splitter splitter) where
  reads := Composition.SignalComponent.inputReads splitter.ports
  writes := Composition.SignalComponent.outputWrites splitter.ports
  determines := by
    intro left right leftSatisfies rightSatisfies _ inputsAgree output _
    exact congrFun (leftSatisfies.trans
      ((congrArg splitter.outputValues
        (Composition.SignalComponent.inputs_equal_of_agree splitter.ports
          _ _ inputsAgree)).trans rightSatisfies.symm)) output

def Composition.SignalSplitter.canonicalHierStep
    (splitter : Composition.SignalSplitter)
    (inputs : splitter.ports.inputs.Values) :
    HierStep (.splitter splitter) :=
  { inputs := inputs
    outputs := splitter.outputValues inputs }

theorem Composition.SignalSplitter.hasSolution
    (splitter : Composition.SignalSplitter) :
    (ModuleStructure.splitter splitter).HasSolution := by
  intro inputs currentState
  refine ⟨splitter.canonicalHierStep inputs, rfl, rfl, ?_⟩
  change SignalMap.emptyValues = currentState
  exact Subsingleton.elim _ _

theorem Composition.SignalSplitter.hasAtMostOneSolution
    (splitter : Composition.SignalSplitter) :
    (ModuleStructure.splitter splitter).HasAtMostOneSolution := by
  intro left right leftSatisfies rightSatisfies inputsEqual _
  cases left
  cases right
  simp_all only [ModuleStructure.IsSolution, HierStep.inputs,
    HierStep.outputs, Composition.SignalSplitter.IsSolution]

def Composition.SignalCombiner.structuralRule
    (combiner : Composition.SignalCombiner) :
    StructuralRule (.combiner combiner) where
  reads := Composition.SignalComponent.inputReads combiner.ports
  writes := Composition.SignalComponent.outputWrites combiner.ports
  determines := by
    intro left right leftSatisfies rightSatisfies _ inputsAgree output _
    exact congrFun (leftSatisfies.trans
      ((congrArg combiner.outputValues
        (Composition.SignalComponent.inputs_equal_of_agree combiner.ports
          _ _ inputsAgree)).trans rightSatisfies.symm)) output

def Composition.SignalCombiner.canonicalHierStep
    (combiner : Composition.SignalCombiner)
    (inputs : combiner.ports.inputs.Values) :
    HierStep (.combiner combiner) :=
  { inputs := inputs
    outputs := combiner.outputValues inputs }

theorem Composition.SignalCombiner.hasSolution
    (combiner : Composition.SignalCombiner) :
    (ModuleStructure.combiner combiner).HasSolution := by
  intro inputs currentState
  refine ⟨combiner.canonicalHierStep inputs, rfl, rfl, ?_⟩
  change SignalMap.emptyValues = currentState
  exact Subsingleton.elim _ _

theorem Composition.SignalCombiner.hasAtMostOneSolution
    (combiner : Composition.SignalCombiner) :
    (ModuleStructure.combiner combiner).HasAtMostOneSolution := by
  intro left right leftSatisfies rightSatisfies inputsEqual _
  cases left
  cases right
  simp_all only [ModuleStructure.IsSolution, HierStep.inputs,
    HierStep.outputs, Composition.SignalCombiner.IsSolution]

end Silean
