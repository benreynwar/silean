import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.VectorSplit

open Silean

/-! Split a vector into its low-index left portion and remaining right portion. -/

def leftPart (value : Fin (leftWidth + rightWidth) → α) : Fin leftWidth → α :=
  fun index => value (Fin.castAdd rightWidth index)

def rightPart (value : Fin (leftWidth + rightWidth) → α) : Fin rightWidth → α :=
  fun index => value (Fin.natAdd leftWidth index)

def splitter (element : SignalType) (leftWidth rightWidth : Nat) :
    Composition.SignalSplitter := .vector (leftWidth + rightWidth) element

def leftCombiner (element : SignalType) (leftWidth : Nat) :
    Composition.SignalCombiner := .vector leftWidth element

def rightCombiner (element : SignalType) (rightWidth : Nat) :
    Composition.SignalCombiner := .vector rightWidth element

end Silean.Modules.VectorSplit

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design VectorSplit (element : SignalType) (leftWidth : Nat) (rightWidth : Nat)
    with (elementNaming : Silean.Naming.SignalTypeNaming element :=
      .positional element) where
  ports {
    input value (schema := .vector elementNaming) : .vector (leftWidth + rightWidth) element,
    output left (schema := .vector elementNaming) : .vector leftWidth element,
    output right (schema := .vector elementNaming) : .vector rightWidth element }
  instances {
    -- Expose every input element.
    split
      (naming := Silean.Naming.SignalAdapter.splitterWithNaming
        (.vector (leftWidth + rightWidth) element) (.vector elementNaming)) :=
      Silean.Naming.SignalAdapter.splitterDesign
        (VectorSplit.splitter element leftWidth rightWidth),
    -- Reassemble the two index ranges. Their emitted names avoid collisions
    -- with the boundary outputs of the same names.
    left (name := "combineLeft")
      (naming := Silean.Naming.SignalAdapter.combinerWithNaming
        (.vector leftWidth element) (.vector elementNaming)) :=
      Silean.Naming.SignalAdapter.combinerDesign
        (VectorSplit.leftCombiner element leftWidth),
    right (name := "combineRight")
      (naming := Silean.Naming.SignalAdapter.combinerWithNaming
        (.vector rightWidth element) (.vector elementNaming)) :=
      Silean.Naming.SignalAdapter.combinerDesign
        (VectorSplit.rightCombiner element rightWidth) }
  wiring {
    outputs {
      .left := left.value,
      .right := right.value }
    instance (.split) {
      .value := input.value }
    instance (.left) {
      index := from ((VectorSplit.context element leftWidth rightWidth).instanceOutput
        .split (Fin.castAdd rightWidth index)) }
    instance (.right) {
      index := from ((VectorSplit.context element leftWidth rightWidth).instanceOutput
        .split (Fin.natAdd leftWidth index)) }
  }

end Silean.Modules

namespace Silean.Modules.VectorSplit

open Silean
open Silean.Authoring

def outputRule (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.CycleOutputRule (ports element leftWidth rightWidth)
      emptySignalMap where
  readsInputs := .all (inputMap element leftWidth rightWidth)
  writesOutputs := .all (outputMap element leftWidth rightWidth)
  target inputs _ := fun
    | .left => leftPart (inputs .value)
    | .right => rightPart (inputs .value)

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
      outputs .left = leftPart (inputs .value) ∧
      outputs .right = rightPart (inputs .value) := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal; exact ⟨congrFun equal .left, congrFun equal .right⟩
  · rintro ⟨left, right⟩; funext output; cases output <;> assumption

theorem left_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs) :
    outputs .left = leftPart (inputs .value) :=
  (outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds |>.1

theorem right_of_holds (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element leftWidth rightWidth).outputs.Values)
    (holds : (outputRule element leftWidth rightWidth).Holds inputs state outputs) :
    outputs .right = rightPart (inputs .value) :=
  (outputRule_holds_iff element leftWidth rightWidth inputs state outputs).mp holds |>.2

end Silean.Modules.VectorSplit
