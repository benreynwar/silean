import Silean.StructuralSemantics

namespace Silean

def InputsAgreeOn {ports : ModulePorts} (reads : List ports.inputs.Label)
    (left right : ports.inputs.Values) : Prop :=
  ∀ input, input ∈ reads → left input = right input

/-! A structural rule is a semantic dependency fact, not a behavioral
contract or an executable program. -/

structure StructuralRule {ports : ModulePorts} (module : ModuleStructure ports) where
  reads : List ports.inputs.Label
  writes : List ports.outputs.Label
  determines : ∀ (leftInputs rightInputs : ports.inputs.Values)
      (currentState : module.State) (left right : ProposedValues module),
    module.IsSolution leftInputs currentState left →
    module.IsSolution rightInputs currentState right →
    InputsAgreeOn reads leftInputs rightInputs →
    ∀ output, output ∈ writes → left.outputs output = right.outputs output

def ModuleStructure.HasAtMostOneSolution {ports : ModulePorts}
    (module : ModuleStructure ports) : Prop :=
  ∀ (inputs : ports.inputs.Values) (currentState : module.State)
    (left right : ProposedValues module),
    module.IsSolution inputs currentState left →
    module.IsSolution inputs currentState right → left = right

def Primitive.ruleReads (primitive : Primitive) :
    List primitive.ports.inputs.Label := primitive.outputReads

def Primitive.ruleWrites (primitive : Primitive) :
    List primitive.ports.outputs.Label := primitive.ports.outputs.labels.values

def Primitive.structuralRule (primitive : Primitive) :
    StructuralRule (ModuleStructure.primitive primitive) where
  reads := primitive.ruleReads
  writes := primitive.ruleWrites
  determines := by
    intro leftInputs rightInputs currentState left right hleft hright hagree output member
    cases left with
    | mk leftOutputs leftNext =>
      cases right with
      | mk rightOutputs rightNext =>
        have outputsEqual := primitive.outputRespectsReads leftInputs rightInputs
          currentState hagree
        simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
          Primitive.IsSolution, Primitive.OutputsSatisfy] at hleft hright
        exact congrFun (hleft.1.trans (outputsEqual.trans hright.1.symm)) output

@[simp] theorem Primitive.structuralRule_writes (primitive : Primitive) :
    primitive.structuralRule.writes = primitive.ruleWrites := rfl

@[simp] theorem Primitive.structuralRule_reads (primitive : Primitive) :
    primitive.structuralRule.reads = primitive.ruleReads := rfl

theorem Primitive.hasAtMostOneSolution (primitive : Primitive) :
    (ModuleStructure.primitive primitive).HasAtMostOneSolution := by
  intro inputs currentState left right leftSatisfies rightSatisfies
  cases left with
  | mk leftOutputs leftNext =>
    cases right with
    | mk rightOutputs rightNext =>
      simp_all only [ModuleStructure.IsSolution,
        ProposedValues.IsSolution, Primitive.IsSolution,
        Primitive.OutputsSatisfy, Primitive.NextStateSatisfy]

def SignalSplitter.structuralRule (splitter : SignalSplitter) :
    StructuralRule (ModuleStructure.splitter splitter) where
  reads := SignalComponent.inputReads splitter.ports
  writes := SignalComponent.outputWrites splitter.ports
  determines := by
    intro leftInputs rightInputs currentState left right
      leftSatisfies rightSatisfies inputsAgree output outputMem
    simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
      SignalSplitter.IsSolution] at leftSatisfies rightSatisfies
    exact congrFun (leftSatisfies.trans
      ((congrArg splitter.outputValues
        (SignalComponent.inputs_equal_of_agree splitter.ports _ _ inputsAgree)).trans
        rightSatisfies.symm)) output

theorem SignalSplitter.hasAtMostOneSolution (splitter : SignalSplitter) :
    (ModuleStructure.splitter splitter).HasAtMostOneSolution := by
  intro inputs currentState left right leftSatisfies rightSatisfies
  simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
    SignalSplitter.IsSolution] at leftSatisfies rightSatisfies
  exact leftSatisfies.trans rightSatisfies.symm

def SignalCombiner.structuralRule (combiner : SignalCombiner) :
    StructuralRule (ModuleStructure.combiner combiner) where
  reads := SignalComponent.inputReads combiner.ports
  writes := SignalComponent.outputWrites combiner.ports
  determines := by
    intro leftInputs rightInputs currentState left right
      leftSatisfies rightSatisfies inputsAgree output outputMem
    simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
      SignalCombiner.IsSolution] at leftSatisfies rightSatisfies
    exact congrFun (leftSatisfies.trans
      ((congrArg combiner.outputValues
        (SignalComponent.inputs_equal_of_agree combiner.ports _ _ inputsAgree)).trans
        rightSatisfies.symm)) output

theorem SignalCombiner.hasAtMostOneSolution (combiner : SignalCombiner) :
    (ModuleStructure.combiner combiner).HasAtMostOneSolution := by
  intro inputs currentState left right leftSatisfies rightSatisfies
  simp only [ModuleStructure.IsSolution, ProposedValues.IsSolution,
    SignalCombiner.IsSolution] at leftSatisfies rightSatisfies
  exact leftSatisfies.trans rightSatisfies.symm

end Silean
