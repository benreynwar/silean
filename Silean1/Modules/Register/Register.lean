import Silean.Composition.LeafwiseComposition
import Silean.Primitives.Register

/-! # Generic register

`Register` stores any signal type. Its public contract exposes the value held
before the clock edge and stores the input on the edge. The recursive
componentwise implementation for aggregate values lives under `Internal/`.
-/

namespace Silean.Modules.Register

open Silean

@[reducible] def interface : Composition.LeafwiseInterface where
  Input := Primitives.UnaryInput
  inputs := inferInstance
  RecursiveInput := PUnit
  recursiveInputs := Enumeration.punit
  FixedInput := NoSignal
  fixedInputs := inferInstance
  inputLayout := {
    classify := fun | .input => .inl .unit
    label := fun | .inl _ => .input | .inr impossible => nomatch impossible
    classify_label := by intro part; cases part with
      | inl value => cases value; rfl
      | inr impossible => exact nomatch impossible
    label_classify := by intro inputName; cases inputName; rfl }
  fixedInputType := fun impossible => nomatch impossible
  Output := Primitives.SingleOutput
  outputs := inferInstance
  State := Primitives.RegisterState
  states := inferInstance

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  interface.inputMap signalType

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  interface.outputMap signalType

@[reducible] def stateMap (signalType : SignalType) : SignalMap :=
  interface.stateMap signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  interface.ports signalType

abbrev Rule := Primitives.RegisterRule

def outputRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (ports signalType) (stateMap signalType) where
  readsInputs := .empty (inputMap signalType)
  writesOutputs := .all (outputMap signalType)
  target _ state := fun | .output => state .stored

def stateRule (signalType : SignalType) :
    Contracts.Cycle.CycleStateRule (ports signalType) (stateMap signalType) where
  readsInputs := .all (inputMap signalType)
  target inputs _ := fun | .stored => inputs .input

@[reducible] def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := stateMap signalType
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => outputRule signalType
  stateRule := stateRule signalType
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (stateMap signalType).Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .output = state .stored := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

section AllowedStep

variable {signalType : SignalType}
  {step : (cycleContract signalType).Step}
  (allowed : (cycleContract signalType).Allows step)

include allowed

/-- A register exposes the value stored before the clock edge. -/
theorem output_of_allowed :
    step.outputs .output = step.currentState .stored :=
  (outputRule_holds_iff signalType
    step.inputs step.currentState step.outputs).mp (allowed.1 .observe)

/-- On the clock edge, a register stores its input. -/
theorem next_stored_of_allowed :
    step.nextState .stored = step.inputs .input := by
  rw [allowed.2]
  rfl

end AllowedStep

end Silean.Modules.Register
