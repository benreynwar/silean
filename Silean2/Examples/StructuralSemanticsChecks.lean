import Silean2.StructuralSemantics
import Silean2.Examples.Not
import Silean2.Modules.BitMux
import Silean2.Examples.RepeatedDualNot

namespace Silean2.Examples.StructuralSemanticsChecks

open Silean2

def emptyLocalState : emptySignalMap.Values :=
  SignalMap.emptyValues

def equalInputs : Primitives.eq.ports.inputs.Values
  | .left | .right => true

def equalOutputs : Primitives.eq.ports.outputs.Values
  | .output => true

example : Primitives.eq.IsSolution equalInputs emptyLocalState emptyLocalState
    equalOutputs := ⟨rfl, rfl⟩

def notInputs : Examples.Not.ports.inputs.Values
  | .value => true

def notState : Examples.Not.moduleStructure.State
  | .inverter => emptyLocalState

def notProposal : ProposedValues Examples.Not.moduleStructure :=
  .composite (fun | .inverted => false)
    (fun
      | .inverter =>
          .primitive (fun | .output => false) emptyLocalState)

example : Examples.Not.moduleStructure.IsSolution notInputs notState notProposal := by
  constructor
  · intro output
    cases output
    rfl
  · intro name
    cases name
    exact ⟨rfl, rfl⟩

def invalidNotProposal : ProposedValues Examples.Not.moduleStructure :=
  .composite (fun | .inverted => true)
    (fun
      | .inverter =>
          .primitive (fun | .output => true) emptyLocalState)

example : ¬Examples.Not.moduleStructure.IsSolution notInputs notState invalidNotProposal := by
  intro satisfies
  have primitiveSatisfies := satisfies.2 Examples.Not.Instance.inverter
  exact Bool.noConfusion (congrFun primitiveSatisfies.1 .output)

def muxInputs : Modules.BitMux.ports.inputs.Values
  | .select => true
  | .whenFalse => false
  | .whenTrue => true

def muxState : Modules.BitMux.moduleStructure.State
  | .invertSelect | .chooseFalse | .chooseTrue | .combine => emptyLocalState

def muxProposal : ProposedValues Modules.BitMux.moduleStructure :=
  .composite (fun | .result => true)
    (fun
      | .invertSelect =>
          .primitive (fun | .output => false) emptyLocalState
      | .chooseFalse =>
          .primitive (fun | .output => false) emptyLocalState
      | .chooseTrue =>
          .primitive (fun | .output => true) emptyLocalState
      | .combine =>
          .primitive (fun | .output => true) emptyLocalState)

example : Modules.BitMux.moduleStructure.IsSolution muxInputs muxState muxProposal := by
  constructor
  · intro output
    cases output
    rfl
  · intro name
    cases name <;> exact ⟨rfl, rfl⟩

def dualInputs : Examples.DualNot.ports.inputs.Values
  | .forward => true
  | .backward => false

def hierarchicalState : Examples.HierarchicalDualNot.moduleStructure.State
  | .forwardNot | .backwardNot => emptyLocalState

def hierarchicalProposal : ProposedValues Examples.HierarchicalDualNot.moduleStructure :=
  .composite (fun | .forward => false | .backward => true)
    (fun
      | .forwardNot =>
          .primitive (fun | .output => false) emptyLocalState
      | .backwardNot =>
          .primitive (fun | .output => true) emptyLocalState)

example : Examples.HierarchicalDualNot.moduleStructure.IsSolution dualInputs hierarchicalState
    hierarchicalProposal := by
  constructor
  · intro output
    cases output <;> rfl
  · intro name
    cases name <;> exact ⟨rfl, rfl⟩

def repeatedState : Examples.RepeatedDualNot.moduleStructure.State
  | .first | .second => hierarchicalState

def secondHierarchicalProposal : ProposedValues Examples.HierarchicalDualNot.moduleStructure :=
  .composite (fun | .forward => true | .backward => false)
    (fun
      | .forwardNot =>
          .primitive (fun | .output => true) emptyLocalState
      | .backwardNot =>
          .primitive (fun | .output => false) emptyLocalState)

def repeatedProposal : ProposedValues Examples.RepeatedDualNot.moduleStructure :=
  .composite (fun | .forward => true | .backward => false)
    (fun
      | .first => hierarchicalProposal
      | .second => secondHierarchicalProposal)

example : Examples.RepeatedDualNot.moduleStructure.IsSolution dualInputs repeatedState
    repeatedProposal := by
  constructor
  · intro output
    cases output <;> rfl
  · intro name
    cases name
    · constructor
      · intro output
        cases output <;> rfl
      · intro childName
        cases childName <;> exact ⟨rfl, rfl⟩
    · constructor
      · intro output
        cases output <;> rfl
      · intro childName
        cases childName <;> exact ⟨rfl, rfl⟩

example : repeatedProposal.nextState = repeatedState := by
  funext name
  cases name <;> funext childName <;> cases childName <;> rfl

end Silean2.Examples.StructuralSemanticsChecks
