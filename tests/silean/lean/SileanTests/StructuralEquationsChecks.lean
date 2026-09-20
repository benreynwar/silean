import Silean.Semantics.StructuralEquations
import SileanTests.Fixtures.Not
import Silean.Modules.BitMux.BitMuxDerived
import SileanTests.Fixtures.RepeatedDualNot

namespace SileanTests.StructuralEquations

open Silean

def emptyLocalState : emptySignalMap.Values :=
  SignalMap.emptyValues

def notLeafStep (value : Bool) :
    HierStep (.primitive Primitives.not) :=
  { inputs := fun | .input => value
    currentState := emptyLocalState
    outputs := fun | .output => !value
    nextState := emptyLocalState }

example (value : Bool) :
    (ModuleStructure.primitive Primitives.not).IsSolution
      (notLeafStep value) :=
  ⟨rfl, rfl⟩

def notInputs : SileanTests.Fixtures.Not.ports.inputs.Values
  | .value => true

def notHierStep : HierStep SileanTests.Fixtures.Not.moduleStructure :=
  { inputs := notInputs
    outputs := fun | .inverted => false
    children := fun | .inverter => notLeafStep true }

example : SileanTests.Fixtures.Not.moduleStructure.IsSolution notHierStep := by
  refine ⟨?_, ?_, ?_⟩
  · intro output
    cases output
    rfl
  · intro name
    cases name
    rfl
  · intro name
    cases name
    exact ⟨rfl, rfl⟩

def invalidNotLeafStep : HierStep (.primitive Primitives.not) :=
  { inputs := fun | .input => true
    currentState := emptyLocalState
    outputs := fun | .output => true
    nextState := emptyLocalState }

def invalidNotHierStep : HierStep SileanTests.Fixtures.Not.moduleStructure :=
  { inputs := notInputs
    outputs := fun | .inverted => true
    children := fun | .inverter => invalidNotLeafStep }

example :
    ¬SileanTests.Fixtures.Not.moduleStructure.IsSolution invalidNotHierStep := by
  intro satisfies
  have primitiveSatisfies := satisfies.2.2
    SileanTests.Fixtures.Not.Instance.inverter
  have impossible := congrFun primitiveSatisfies.1 .output
  change true = false at impossible
  exact Bool.noConfusion impossible

def muxInputs : Modules.BitMux.ports.inputs.Values
  | .select => true
  | .whenFalse => false
  | .whenTrue => true

def muxHierStep : HierStep Modules.BitMux.moduleStructure :=
  { inputs := muxInputs
    outputs := fun | .result => true
    children := fun
      | .invertSelect =>
          { inputs := fun | .input => true
            currentState := emptyLocalState
            outputs := fun | .output => false
            nextState := emptyLocalState }
      | .chooseFalse =>
          { inputs := fun | .left => false | .right => false
            currentState := emptyLocalState
            outputs := fun | .output => false
            nextState := emptyLocalState }
      | .chooseTrue =>
          { inputs := fun | .left => true | .right => true
            currentState := emptyLocalState
            outputs := fun | .output => true
            nextState := emptyLocalState }
      | .combine =>
          { inputs := fun | .left => false | .right => true
            currentState := emptyLocalState
            outputs := fun | .output => true
            nextState := emptyLocalState } }

example : Modules.BitMux.moduleStructure.IsSolution muxHierStep := by
  refine ⟨?_, ?_, ?_⟩
  · intro output
    cases output
    rfl
  · intro name
    cases name <;> funext port <;> cases port <;> rfl
  · intro name
    cases name <;> exact ⟨rfl, rfl⟩

def dualInputs : SileanTests.Fixtures.DualNot.ports.inputs.Values
  | .forward => true
  | .backward => false

def firstDualStep :
    HierStep SileanTests.Fixtures.HierarchicalDualNot.moduleStructure :=
  { inputs := dualInputs
    outputs := fun | .forward => false | .backward => true
    children := fun
      | .forwardNot => notLeafStep true
      | .backwardNot => notLeafStep false }

def secondDualStep :
    HierStep SileanTests.Fixtures.HierarchicalDualNot.moduleStructure :=
  { inputs := fun | .forward => false | .backward => true
    outputs := fun | .forward => true | .backward => false
    children := fun
      | .forwardNot => notLeafStep false
      | .backwardNot => notLeafStep true }

def repeatedHierStep :
    HierStep SileanTests.Fixtures.RepeatedDualNot.moduleStructure :=
  { inputs := dualInputs
    outputs := fun | .forward => true | .backward => false
    children := fun
      | .first => firstDualStep
      | .second => secondDualStep }

example :
    SileanTests.Fixtures.RepeatedDualNot.moduleStructure.IsSolution
      repeatedHierStep := by
  refine ⟨?_, ?_, ?_⟩
  · intro output
    cases output <;> rfl
  · intro name
    cases name <;> funext port <;> cases port <;> rfl
  · intro name
    cases name
    · refine ⟨?_, ?_, ?_⟩
      · intro output
        cases output <;> rfl
      · intro child
        cases child <;> funext port <;> cases port <;> rfl
      · intro child
        cases child <;> exact ⟨rfl, rfl⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro output
        cases output <;> rfl
      · intro child
        cases child <;> funext port <;> cases port <;> rfl
      · intro child
        cases child <;> exact ⟨rfl, rfl⟩

example :
    HierStep.nextState SileanTests.Fixtures.RepeatedDualNot.moduleStructure
      repeatedHierStep =
      HierStep.currentState
        SileanTests.Fixtures.RepeatedDualNot.moduleStructure repeatedHierStep := by
  funext name
  cases name <;> simp [SileanTests.Fixtures.RepeatedDualNot.moduleStructure,
    SileanTests.Fixtures.RepeatedDualNot.childStructure,
    SileanTests.Fixtures.HierarchicalDualNot.moduleStructure,
    SileanTests.Fixtures.HierarchicalDualNot.children,
    Contracts.Cycle.Certification.Layer.moduleStructure,
    Contracts.Cycle.ModuleCycleCertified.certifiedStructure,
    Primitives.notCertified, HierStep.nextState, HierStep.currentState,
    repeatedHierStep, firstDualStep, secondDualStep, notLeafStep] <;>
    funext child <;> cases child <;>
    simp [HierStep.nextState, HierStep.currentState]

end SileanTests.StructuralEquations
