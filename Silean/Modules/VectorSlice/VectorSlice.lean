import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Authoring.CircuitDescription
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules.VectorSlice

open Silean

/-! Extract a contiguous vector range. `prefixWidth` elements precede the
result and `suffixWidth` elements follow it. The circuit is a dependent index
mapping between generic adapters, which the typed `module_design` states more
directly than a duplicated builder description would. -/

def slice (value : Fin (prefixWidth + width + suffixWidth) → α) : Fin width → α :=
  fun index => value (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index))

def splitter (element : SignalType) (prefixWidth width suffixWidth : Nat) :
    Composition.SignalSplitter :=
  .vector (prefixWidth + width + suffixWidth) element

def combiner (element : SignalType) (width : Nat) : Composition.SignalCombiner :=
  .vector width element

end Silean.Modules.VectorSlice

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design VectorSlice (element : SignalType) (prefixWidth : Nat)
    (width : Nat) (suffixWidth : Nat)
    with (elementNaming : Silean.Naming.SignalTypeNaming element :=
      .positional element) where
  ports {
    input value (schema := .vector elementNaming) :
      .vector (prefixWidth + width + suffixWidth) element,
    output result (schema := .vector elementNaming) : .vector width element }
  instances {
    -- Expose every source element.
    split
      (naming := Silean.Naming.SignalAdapter.splitterWithNaming
        (.vector (prefixWidth + width + suffixWidth) element)
        (.vector elementNaming)) :=
      Silean.Naming.SignalAdapter.splitterDesign
        (VectorSlice.splitter element prefixWidth width suffixWidth),
    -- Collect just the selected contiguous range.
    combine
      (naming := Silean.Naming.SignalAdapter.combinerWithNaming
        (.vector width element) (.vector elementNaming)) :=
      Silean.Naming.SignalAdapter.combinerDesign
        (VectorSlice.combiner element width) }
  wiring {
    outputs {
      .result := combine.value }
    instance (.split) {
      .value := input.value }
    instance (.combine) {
      index := from ((VectorSlice.context element prefixWidth width suffixWidth).instanceOutput
        .split (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index))) }
  }

end Silean.Modules

namespace Silean.Modules.VectorSlice

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

/-! ## Placement -/

noncomputable def placeNamed (name : Naming.SourceName)
    (element : SignalType) (prefixWidth width suffixWidth : Nat)
    (value : Net (.vector (prefixWidth + width + suffixWidth) element)) :
    Builder (Net (.vector width element)) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (design element prefixWidth width suffixWidth) fun | .value => value
  pure (child .result)

noncomputable def place (element : SignalType)
    (prefixWidth width suffixWidth : Nat)
    (value : Net (.vector (prefixWidth + width + suffixWidth) element)) :
    Builder (Net (.vector width element)) := do
  let child ← placeIndexed "vector_slice"
    (design element prefixWidth width suffixWidth) fun | .value => value
  pure (child .result)

attribute [circuit_description] placeNamed place

def outputRule (element : SignalType) (prefixWidth width suffixWidth : Nat) :
    Contracts.Cycle.CycleOutputRule
      (ports element prefixWidth width suffixWidth) emptySignalMap where
  readsInputs := .all (inputMap element prefixWidth width suffixWidth)
  writesOutputs := .all (outputMap element prefixWidth width suffixWidth)
  target inputs _ := fun | .result => slice (inputs .value)

module_cycle_contract cycleContract (element : SignalType)
    (prefixWidth : Nat) (width : Nat) (suffixWidth : Nat)
    for ports element prefixWidth width suffixWidth where
  state := emptySignalMap
  output_rule apply := outputRule element prefixWidth width suffixWidth
  state_rule := Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (element : SignalType)
    (prefixWidth width suffixWidth : Nat)
    (inputs : (ports element prefixWidth width suffixWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element prefixWidth width suffixWidth).outputs.Values) :
    (outputRule element prefixWidth width suffixWidth).Holds inputs state outputs ↔
      outputs .result = slice (inputs .value) := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal; exact congrFun equal .result
  · intro equal; funext output; cases output; exact equal

theorem result_at_of_holds (element : SignalType)
    (prefixWidth width suffixWidth : Nat)
    (inputs : (ports element prefixWidth width suffixWidth).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (ports element prefixWidth width suffixWidth).outputs.Values)
    (holds : (outputRule element prefixWidth width suffixWidth).Holds inputs state outputs)
    (index : Fin width) :
    outputs .result index =
      inputs .value (Fin.castAdd suffixWidth (Fin.natAdd prefixWidth index)) := by
  rw [(outputRule_holds_iff element prefixWidth width suffixWidth
    inputs state outputs).mp holds]
  rfl

/-- Every contract-allowed slice step returns the selected contiguous range. -/
theorem result_of_allowed (element : SignalType)
    (prefixWidth width suffixWidth : Nat)
    {step : (cycleContract element prefixWidth width suffixWidth).Step}
    (allowed : (cycleContract element prefixWidth width suffixWidth).Allows step) :
    step.outputs .result = slice (step.inputs .value) :=
  (outputRule_holds_iff element prefixWidth width suffixWidth
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

end Silean.Modules.VectorSlice
