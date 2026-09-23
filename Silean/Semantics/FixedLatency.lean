import Silean.Semantics.BoundaryTrace

namespace Silean.FixedLatency

/-! # Fixed-latency relations

`Relates` describes a value produced a fixed number of cycles after an input.
It is independent of module ports and state, which makes its serial laws
usable between internal pipeline stages. `Holds` applies the same relation to
the observable input and output projections of a `BoundaryTrace`.
-/

/-- Relational composition used by serial fixed-latency stages. -/
def Comp {α β γ : Type} (left : α → β → Prop) (right : β → γ → Prop)
    (input : α) (output : γ) : Prop :=
  ∃ intermediate, left input intermediate ∧ right intermediate output

/-- Equal-length value sequences related with a fixed cycle displacement. -/
def Relates {α β : Type} (latency : Nat) (relation : α → β → Prop)
    (inputs : List α) (outputs : List β) : Prop :=
  outputs.length = inputs.length ∧
    ∀ (t : Nat) (inputInTrace : t < inputs.length)
        (outputInTrace : t + latency < outputs.length),
      relation
        (inputs.get ⟨t, inputInTrace⟩)
        (outputs.get ⟨t + latency, outputInTrace⟩)

/-- A fixed-latency relation on the observable boundary trace of one module. -/
def Holds {ports : ModulePorts} (latency : Nat)
    (relation : ports.inputs.Values → ports.outputs.Values → Prop)
    (trace : BoundaryTrace ports) : Prop :=
  Relates latency relation trace.inputs trace.outputs

/-- A deterministic specialization of `Relates`. -/
def Computes (latency : Nat) (function : α → β)
    (inputs : List α) (outputs : List β) : Prop :=
  Relates latency (fun input output => output = function input) inputs outputs

/-- Project a deterministic port-record contract onto the payload sequences
selected from its input and output records.  This is the standard bridge from
a public module contract to the value-level computations used for serial
composition. -/
theorem computes_of_holds_projection
    {ports : ModulePorts} {latency : Nat} {α β : Type}
    {function : α → β} {trace : BoundaryTrace ports}
    (inputProjection : ports.inputs.Values → α)
    (outputProjection : ports.outputs.Values → β)
    (holds : Holds latency
      (fun input output =>
        outputProjection output = function (inputProjection input)) trace) :
    Computes latency function
      (trace.inputs.map inputProjection)
      (trace.outputs.map outputProjection) := by
  unfold Holds Relates at holds
  unfold Computes Relates
  constructor
  · simpa only [List.length_map] using holds.1
  · intro t inputInTrace outputInTrace
    have originalInputInTrace : t < trace.inputs.length := by
      simpa using inputInTrace
    have originalOutputInTrace : t + latency < trace.outputs.length := by
      simpa using outputInTrace
    have related := holds.2 t originalInputInTrace originalOutputInTrace
    simpa only [List.get_eq_getElem, List.getElem_map] using related

/-- Read a fixed-latency relation at one valid delayed position. -/
theorem relation_at
    {α β : Type} {latency : Nat} {relation : α → β → Prop}
    {inputs : List α} {outputs : List β}
    (holds : Relates latency relation inputs outputs)
    (t : Nat) (outputInTrace : t + latency < outputs.length) :
    relation
      (inputs.get ⟨t, by
        have := holds.1
        omega⟩)
      (outputs.get ⟨t + latency, outputInTrace⟩) :=
  holds.2 t (by
    have lengths := holds.1
    omega) outputInTrace

/-- Read a fixed-latency module relation using the length of its boundary
trace rather than either projected list. -/
theorem boundary_relation_at
    {ports : ModulePorts} {latency : Nat}
    {relation : ports.inputs.Values → ports.outputs.Values → Prop}
    {trace : BoundaryTrace ports}
    (holds : Holds latency relation trace)
    (t : Nat) (outputInTrace : t + latency < trace.length) :
    relation
      (trace.inputs.get ⟨t, by
        have inTrace : t < trace.length := by omega
        simpa using inTrace⟩)
      (trace.outputs.get ⟨t + latency, by simpa using outputInTrace⟩) := by
  exact relation_at holds t (by simpa using outputInTrace)

/-- Apply a boundary-trace contract directly to the original input and output
lists of the state-threaded trace from which that boundary trace was erased. -/
theorem relation_at_of_trace
    {ports : ModulePorts} {State : Type}
    {Step : ports.inputs.Values → State →
      ports.outputs.Values → State → Prop}
    {initialState finalState : State}
    {inputs : List ports.inputs.Values}
    {outputs : List ports.outputs.Values}
    {latency : Nat}
    {relation : ports.inputs.Values → ports.outputs.Values → Prop}
    (trace : Trace Step initialState inputs outputs finalState)
    (holds : Holds latency relation trace.toBoundaryTrace)
    (t : Nat) (inputInTrace : t < inputs.length)
    (outputInTrace : t + latency < outputs.length) :
    relation
      (inputs.get ⟨t, inputInTrace⟩)
      (outputs.get ⟨t + latency, outputInTrace⟩) := by
  change Relates latency relation trace.toBoundaryTrace.inputs
    trace.toBoundaryTrace.outputs at holds
  have traceInputInTrace : t < trace.toBoundaryTrace.inputs.length := by
    rw [trace.toBoundaryTrace_inputs]
    exact inputInTrace
  have traceOutputInTrace :
      t + latency < trace.toBoundaryTrace.outputs.length := by
    rw [trace.toBoundaryTrace_outputs]
    exact outputInTrace
  have observed :=
    holds.2 t traceInputInTrace traceOutputInTrace
  simpa only [List.get_eq_getElem, Trace.toBoundaryTrace_inputs,
    Trace.toBoundaryTrace_outputs] using observed

/-- A zero-latency relation holds pointwise at every trace position. -/
theorem zero_apply
    {α β : Type} {relation : α → β → Prop}
    {inputs : List α} {outputs : List β}
    (holds : Relates 0 relation inputs outputs)
    (t : Nat) (inTrace : t < outputs.length) :
    relation
      (inputs.get ⟨t, by
        have := holds.1
        omega⟩)
      (outputs.get ⟨t, inTrace⟩) := by
  simpa using relation_at holds t (by simpa using inTrace)

/-- Serial composition adds the two stage latencies. -/
theorem serial
    {α β γ : Type}
    {leftLatency rightLatency : Nat}
    {leftRelation : α → β → Prop}
    {rightRelation : β → γ → Prop}
    {inputs : List α} {intermediate : List β} {outputs : List γ}
    (left : Relates leftLatency leftRelation inputs intermediate)
    (right : Relates rightLatency rightRelation intermediate outputs) :
    Relates (leftLatency + rightLatency)
      (Comp leftRelation rightRelation) inputs outputs := by
  constructor
  · exact right.1.trans left.1
  · intro t inputInTrace outputInTrace
    have intermediateInTrace : t + leftLatency < intermediate.length := by
      rw [← right.1]
      omega
    have leftHolds := relation_at left t intermediateInTrace
    have rightOutputInTrace :
        (t + leftLatency) + rightLatency < outputs.length := by
      omega
    have rightHolds :=
      relation_at right (t + leftLatency) rightOutputInTrace
    refine ⟨intermediate.get ⟨t + leftLatency, intermediateInTrace⟩,
      leftHolds, ?_⟩
    simpa [Nat.add_assoc] using rightHolds

/-- Serial composition of deterministic fixed-latency stages adds latencies
and composes their functions. -/
theorem computes_serial
    {α β γ : Type}
    {leftLatency rightLatency : Nat}
    {leftFunction : α → β} {rightFunction : β → γ}
    {inputs : List α} {intermediate : List β} {outputs : List γ}
    (left : Computes leftLatency leftFunction inputs intermediate)
    (right : Computes rightLatency rightFunction intermediate outputs) :
    Computes (leftLatency + rightLatency)
      (rightFunction ∘ leftFunction) inputs outputs := by
  unfold Computes at left right ⊢
  refine ⟨right.1.trans left.1, ?_⟩
  intro t inputInTrace outputInTrace
  have intermediateInTrace : t + leftLatency < intermediate.length := by
    rw [← right.1]
    omega
  have leftHolds := left.2 t inputInTrace intermediateInTrace
  have rightInputInTrace : t + leftLatency < intermediate.length :=
    intermediateInTrace
  have rightOutputInTrace :
      (t + leftLatency) + rightLatency < outputs.length := by
    omega
  have rightHolds := right.2 (t + leftLatency) rightInputInTrace
    rightOutputInTrace
  have composed := rightHolds.trans (congrArg rightFunction leftHolds)
  simpa only [List.get_eq_getElem, Nat.add_assoc,
    Function.comp_apply] using composed

/-- Apply a combinational function pointwise to the output sequence of a
deterministic fixed-latency computation. -/
theorem computes_map_outputs
    {α β γ : Type} {latency : Nat}
    {function : α → β} {inputs : List α} {outputs : List β}
    (holds : Computes latency function inputs outputs)
    (mapOutput : β → γ) :
    Computes latency (mapOutput ∘ function) inputs
      (outputs.map mapOutput) := by
  unfold Computes at holds ⊢
  constructor
  · simpa using holds.1
  · intro t inputInTrace outputInTrace
    have originalOutputInTrace : t + latency < outputs.length := by
      simpa using outputInTrace
    have original := holds.2 t inputInTrace originalOutputInTrace
    have mapped := congrArg mapOutput original
    simpa only [List.get_eq_getElem, List.getElem_map,
      Function.comp_apply] using mapped

/-- Re-express a computation whose input sequence was produced by a
pointwise combinational map. -/
theorem computes_map_inputs
    {α β γ : Type} {latency : Nat}
    {function : β → γ} {inputs : List α} {outputs : List γ}
    (mapInput : α → β)
    (holds : Computes latency function (inputs.map mapInput) outputs) :
    Computes latency (function ∘ mapInput) inputs outputs := by
  unfold Computes at holds ⊢
  constructor
  · simpa using holds.1
  · intro t inputInTrace outputInTrace
    have mappedInputInTrace : t < (inputs.map mapInput).length := by
      simpa using inputInTrace
    have original := holds.2 t mappedInputInTrace outputInTrace
    simpa only [List.get_eq_getElem, List.getElem_map,
      Function.comp_apply] using original

/-- Synchronize two deterministic computations with the same input sequence
and latency. -/
theorem computes_parallel
    {α β γ : Type} {latency : Nat}
    {leftFunction : α → β} {rightFunction : α → γ}
    {inputs : List α} {leftOutputs : List β} {rightOutputs : List γ}
    (left : Computes latency leftFunction inputs leftOutputs)
    (right : Computes latency rightFunction inputs rightOutputs) :
    Computes latency (fun input =>
      (leftFunction input, rightFunction input)) inputs
      (leftOutputs.zip rightOutputs) := by
  unfold Computes at left right ⊢
  constructor
  · simp [List.length_zip, left.1, right.1]
  · intro t inputInTrace outputInTrace
    have leftOutputInTrace : t + latency < leftOutputs.length := by
      simpa [List.length_zip, left.1, right.1] using outputInTrace
    have rightOutputInTrace : t + latency < rightOutputs.length := by
      simpa [List.length_zip, left.1, right.1] using outputInTrace
    have leftHolds := left.2 t inputInTrace leftOutputInTrace
    have rightHolds := right.2 t inputInTrace rightOutputInTrace
    have paired :
        (leftOutputs.get ⟨t + latency, leftOutputInTrace⟩,
          rightOutputs.get ⟨t + latency, rightOutputInTrace⟩) =
        (leftFunction (inputs.get ⟨t, inputInTrace⟩),
          rightFunction (inputs.get ⟨t, inputInTrace⟩)) := by
      rw [leftHolds, rightHolds]
    simpa only [List.get_eq_getElem, List.getElem_zip] using paired

/-- Replace a computation's output sequence by an equal sequence. -/
theorem computes_congr_outputs
    {α β : Type} {latency : Nat} {function : α → β}
    {inputs : List α} {leftOutputs rightOutputs : List β}
    (equal : leftOutputs = rightOutputs)
    (holds : Computes latency function inputs leftOutputs) :
    Computes latency function inputs rightOutputs := by
  subst rightOutputs
  exact holds

/-- Replace a computation's input sequence by an equal sequence. -/
theorem computes_congr_inputs
    {α β : Type} {latency : Nat} {function : α → β}
    {leftInputs rightInputs : List α} {outputs : List β}
    (equal : leftInputs = rightInputs)
    (holds : Computes latency function leftInputs outputs) :
    Computes latency function rightInputs outputs := by
  subst rightInputs
  exact holds

/-- Two relations with the same latency and sequences can be synchronized
pointwise. -/
theorem and
    {α β : Type} {latency : Nat}
    {leftRelation rightRelation : α → β → Prop}
    {inputs : List α} {outputs : List β}
    (left : Relates latency leftRelation inputs outputs)
    (right : Relates latency rightRelation inputs outputs) :
    Relates latency
      (fun input output =>
        leftRelation input output ∧ rightRelation input output)
      inputs outputs := by
  refine ⟨left.1, ?_⟩
  intro t inputInTrace outputInTrace
  exact ⟨left.2 t inputInTrace outputInTrace,
    right.2 t inputInTrace outputInTrace⟩

end Silean.FixedLatency
