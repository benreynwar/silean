import Silean.Foundation.BoundaryStep
import Silean.Semantics.Trace

namespace Silean

/-! # Observable module traces

A `BoundaryTrace` is a sequence of state-free module-boundary observations.
`Trace.toBoundaryTrace` erases threaded state and transition evidence from an
existing relational execution while retaining every cycle's paired inputs and
outputs.
-/

/-- A finite sequence of externally visible module cycles. -/
abbrev BoundaryTrace (ports : ModulePorts) := List (BoundaryStep ports)

namespace BoundaryTrace

private def pairLists {ports : ModulePorts}
    (inputValues : List ports.inputs.Values)
    (outputValues : List ports.outputs.Values) : BoundaryTrace ports :=
  match inputValues, outputValues with
  | input :: remainingInputs, output :: remainingOutputs =>
      { inputs := input, outputs := output } ::
        pairLists remainingInputs remainingOutputs
  | _, _ => []

/-- Pair equal-length input and output sequences into observable boundary
steps. The length proof prevents silently dropping unmatched cycles. -/
def ofLists {ports : ModulePorts}
    (inputValues : List ports.inputs.Values)
    (outputValues : List ports.outputs.Values)
    (_lengths : inputValues.length = outputValues.length) :
    BoundaryTrace ports :=
  pairLists inputValues outputValues

/-- The input sequence observed by a boundary trace. -/
def inputs {ports : ModulePorts}
    (trace : BoundaryTrace ports) : List ports.inputs.Values :=
  trace.map BoundaryStep.inputs

/-- The output sequence observed by a boundary trace. -/
def outputs {ports : ModulePorts}
    (trace : BoundaryTrace ports) : List ports.outputs.Values :=
  trace.map BoundaryStep.outputs

@[simp] theorem inputs_nil {ports : ModulePorts} :
    inputs ([] : BoundaryTrace ports) = [] :=
  rfl

@[simp] theorem outputs_nil {ports : ModulePorts} :
    outputs ([] : BoundaryTrace ports) = [] :=
  rfl

@[simp] theorem inputs_cons {ports : ModulePorts}
    (step : BoundaryStep ports) (trace : BoundaryTrace ports) :
    inputs (step :: trace) = step.inputs :: inputs trace :=
  rfl

@[simp] theorem outputs_cons {ports : ModulePorts}
    (step : BoundaryStep ports) (trace : BoundaryTrace ports) :
    outputs (step :: trace) = step.outputs :: outputs trace :=
  rfl

@[simp] theorem inputs_length {ports : ModulePorts}
    (trace : BoundaryTrace ports) :
    trace.inputs.length = trace.length := by
  simp [inputs]

@[simp] theorem outputs_length {ports : ModulePorts}
    (trace : BoundaryTrace ports) :
    trace.outputs.length = trace.length := by
  simp [outputs]

/-- A boundary trace is determined by its input and output sequences. -/
@[ext] theorem ext {ports : ModulePorts}
    {left right : BoundaryTrace ports}
    (inputsEqual : left.inputs = right.inputs)
    (outputsEqual : left.outputs = right.outputs) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons _ _ => simp at inputsEqual
  | cons leftStep leftRest induction =>
      cases right with
      | nil => simp at inputsEqual
      | cons rightStep rightRest =>
          simp only [inputs_cons, List.cons.injEq] at inputsEqual
          simp only [outputs_cons, List.cons.injEq] at outputsEqual
          rcases inputsEqual with ⟨headInputs, tailInputs⟩
          rcases outputsEqual with ⟨headOutputs, tailOutputs⟩
          have headEqual : leftStep = rightStep := by
            cases leftStep
            cases rightStep
            simp_all
          subst rightStep
          have tailEqual := induction tailInputs tailOutputs
          subst rightRest
          rfl

@[simp] theorem ofLists_inputs {ports : ModulePorts}
    {inputValues : List ports.inputs.Values}
    {outputValues : List ports.outputs.Values}
    (lengths : inputValues.length = outputValues.length) :
    (ofLists inputValues outputValues lengths).inputs = inputValues := by
  induction inputValues generalizing outputValues with
  | nil =>
      cases outputValues with
      | nil => rfl
      | cons _ _ => simp at lengths
  | cons input remainingInputs induction =>
      cases outputValues with
      | nil => simp at lengths
      | cons output remainingOutputs =>
          have tailLengths :
              remainingInputs.length = remainingOutputs.length :=
            Nat.add_right_cancel lengths
          change input :: (pairLists remainingInputs remainingOutputs).inputs =
            input :: remainingInputs
          simpa [ofLists, pairLists] using
            congrArg (List.cons input) (induction tailLengths)

@[simp] theorem ofLists_outputs {ports : ModulePorts}
    {inputValues : List ports.inputs.Values}
    {outputValues : List ports.outputs.Values}
    (lengths : inputValues.length = outputValues.length) :
    (ofLists inputValues outputValues lengths).outputs = outputValues := by
  induction inputValues generalizing outputValues with
  | nil =>
      cases outputValues with
      | nil => rfl
      | cons _ _ => simp at lengths
  | cons input remainingInputs induction =>
      cases outputValues with
      | nil => simp at lengths
      | cons output remainingOutputs =>
          have tailLengths :
              remainingInputs.length = remainingOutputs.length :=
            Nat.add_right_cancel lengths
          change output :: (pairLists remainingInputs remainingOutputs).outputs =
            output :: remainingOutputs
          simpa [ofLists, pairLists] using
            congrArg (List.cons output) (induction tailLengths)

end BoundaryTrace

namespace Trace

/-- Erase state and transition evidence from a relational trace, retaining
the paired input and observation from every cycle. The trace proof supplies
the invariant that the two underlying sequences have equal length. -/
def toBoundaryTrace
    {ports : ModulePorts}
    {Step : ports.inputs.Values → State →
      ports.outputs.Values → State → Prop}
    {initialState finalState : State}
    {inputValues : List ports.inputs.Values}
    {outputValues : List ports.outputs.Values}
    (trace : Trace Step initialState inputValues outputValues finalState) :
    BoundaryTrace ports :=
  BoundaryTrace.ofLists inputValues outputValues trace.length_eq.symm

@[simp] theorem toBoundaryTrace_inputs
    {ports : ModulePorts}
    {Step : ports.inputs.Values → State →
      ports.outputs.Values → State → Prop}
    {initialState finalState : State}
    {inputValues : List ports.inputs.Values}
    {outputValues : List ports.outputs.Values}
    (trace : Trace Step initialState inputValues outputValues finalState) :
    trace.toBoundaryTrace.inputs = inputValues := by
  apply BoundaryTrace.ofLists_inputs

@[simp] theorem toBoundaryTrace_outputs
    {ports : ModulePorts}
    {Step : ports.inputs.Values → State →
      ports.outputs.Values → State → Prop}
    {initialState finalState : State}
    {inputValues : List ports.inputs.Values}
    {outputValues : List ports.outputs.Values}
    (trace : Trace Step initialState inputValues outputValues finalState) :
    trace.toBoundaryTrace.outputs = outputValues := by
  apply BoundaryTrace.ofLists_outputs

@[simp] theorem toBoundaryTrace_nil
    {ports : ModulePorts}
    {Step : ports.inputs.Values → State →
      ports.outputs.Values → State → Prop}
    (state : State) :
    (Trace.nil (Step := Step) state).toBoundaryTrace = [] := by
  apply BoundaryTrace.ext <;> simp

@[simp] theorem toBoundaryTrace_cons
    {ports : ModulePorts}
    {Step : ports.inputs.Values → State →
      ports.outputs.Values → State → Prop}
    {currentState nextState finalState : State}
    {remainingInputs : List ports.inputs.Values}
    {remainingOutputs : List ports.outputs.Values}
    (input : ports.inputs.Values) (output : ports.outputs.Values)
    (transition : Step input currentState output nextState)
    (rest : Trace Step nextState remainingInputs remainingOutputs finalState) :
    (Trace.cons input output transition rest).toBoundaryTrace =
      { inputs := input, outputs := output } :: rest.toBoundaryTrace := by
  apply BoundaryTrace.ext <;> simp

@[simp] theorem toBoundaryTrace_length
    {ports : ModulePorts}
    {Step : ports.inputs.Values → State →
      ports.outputs.Values → State → Prop}
    {initialState finalState : State}
    {inputValues : List ports.inputs.Values}
    {outputValues : List ports.outputs.Values}
    (trace : Trace Step initialState inputValues outputValues finalState) :
    trace.toBoundaryTrace.length = inputValues.length := by
  rw [← trace.toBoundaryTrace.inputs_length,
    trace.toBoundaryTrace_inputs]

end Trace

end Silean
