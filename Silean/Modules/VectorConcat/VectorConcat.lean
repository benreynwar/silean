import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.VectorConcat

open Silean

/-! Concatenates two vectors of the same element type, with the left vector at
the lower result indices. Its wiring is an index-family transformation rather
than a fixed list of scalar connections. The typed `module_design` keeps that
mapping explicit, so it remains the primary definition instead of duplicating
it with a builder description. -/

def concat (left : Fin leftWidth → α) (right : Fin rightWidth → α) :
    Fin (leftWidth + rightWidth) → α :=
  Fin.addCases left right

@[simp] theorem concat_left (left : Fin leftWidth → α)
    (right : Fin rightWidth → α) (index : Fin leftWidth) :
    concat left right (Fin.castAdd rightWidth index) = left index := by
  simp [concat]

@[simp] theorem concat_right (left : Fin leftWidth → α)
    (right : Fin rightWidth → α) (index : Fin rightWidth) :
    concat left right (Fin.natAdd leftWidth index) = right index := by
  simp [concat]

def leftSplitter (element : SignalType) (leftWidth : Nat) :
    Composition.SignalSplitter :=
  .vector leftWidth element

def rightSplitter (element : SignalType) (rightWidth : Nat) :
    Composition.SignalSplitter :=
  .vector rightWidth element

def combiner (element : SignalType) (leftWidth rightWidth : Nat) :
    Composition.SignalCombiner :=
  .vector (leftWidth + rightWidth) element

end Silean.Modules.VectorConcat
namespace Silean.Modules

open Silean
open Silean.Authoring

/-! ## Hardware structure -/

module_design VectorConcat (element : SignalType) (leftWidth : Nat) (rightWidth : Nat)
    with (elementNaming : Silean.Naming.SignalTypeNaming element :=
      .positional element) where
  ports {
    input left (schema := .vector elementNaming) : .vector leftWidth element,
    input right (schema := .vector elementNaming) : .vector rightWidth element,
    output result (schema := .vector elementNaming) :
      .vector (leftWidth + rightWidth) element }
  instances {
    -- Expose the elements of both input vectors.
    leftSplit
      (naming := Silean.Naming.SignalAdapter.splitterWithNaming
        (.vector leftWidth element) (.vector elementNaming)) :=
      Silean.Naming.SignalAdapter.splitterDesign
        (VectorConcat.leftSplitter element leftWidth),
    rightSplit
      (naming := Silean.Naming.SignalAdapter.splitterWithNaming
        (.vector rightWidth element) (.vector elementNaming)) :=
      Silean.Naming.SignalAdapter.splitterDesign
        (VectorConcat.rightSplitter element rightWidth),
    -- Collect the left elements followed by the right elements.
    combine
      (naming := Silean.Naming.SignalAdapter.combinerWithNaming
        (.vector (leftWidth + rightWidth) element) (.vector elementNaming)) :=
      Silean.Naming.SignalAdapter.combinerDesign
        (VectorConcat.combiner element leftWidth rightWidth) }
  wiring {
    outputs {
      .result := combine.value }
    instance (.leftSplit) {
      .value := input.left }
    instance (.rightSplit) {
      .value := input.right }
    instance (.combine) {
      index := from (Fin.addCases
        (fun leftIndex =>
          (VectorConcat.context element leftWidth rightWidth).instanceOutput
            .leftSplit leftIndex)
        (fun rightIndex =>
          (VectorConcat.context element leftWidth rightWidth).instanceOutput
            .rightSplit rightIndex)
        index) }
  }

end Silean.Modules

namespace Silean.Modules.VectorConcat

open Silean
open Silean.Authoring

/-! ## Exact cycle behavior -/

def outputRule (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.CycleOutputRule (ports element leftWidth rightWidth)
      emptySignalMap where
  readsInputs := .all (inputMap element leftWidth rightWidth)
  writesOutputs := .all (outputMap element leftWidth rightWidth)
  target inputs _ := fun | .result => concat (inputs .left) (inputs .right)

module_cycle_contract cycleContract (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat) for ports element leftWidth rightWidth where
  state := emptySignalMap
  output_rule apply := outputRule element leftWidth rightWidth
  state_rule := Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (element : SignalType)
    (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values) :
    (outputRule element leftWidth rightWidth).Holds inputs state outputs ↔
      outputs .result = concat (inputs .left) (inputs .right) := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .result
  · intro equal
    funext label
    cases label
    exact equal

theorem result_left_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs)
    (index : Fin leftWidth) :
    outputs .result (Fin.castAdd rightWidth index) = inputs .left index := by
  rw [(outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds]
  exact concat_left _ _ index

theorem result_right_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs)
    (index : Fin rightWidth) :
    outputs .result (Fin.natAdd leftWidth index) = inputs .right index := by
  rw [(outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds]
  exact concat_right _ _ index

/-- Every contract-allowed concatenation step joins the left and right input
vectors in order. -/
theorem result_of_allowed (element : SignalType) (leftWidth rightWidth : Nat)
    {step : (cycleContract element leftWidth rightWidth).Step}
    (allowed : (cycleContract element leftWidth rightWidth).Allows step) :
    step.outputs .result = concat (step.inputs .left) (step.inputs .right) :=
  (outputRule_holds_iff element leftWidth rightWidth
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

end Silean.Modules.VectorConcat
