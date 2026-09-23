import Silean.Semantics.FixedLatency

namespace Silean.FramedLatency

/-! # Fixed-latency framed relations

`FixedLatency` describes modules whose output at one cycle depends on the
input at one earlier cycle.  A streaming transform instead consumes and
produces a fixed number of consecutive cycles.  This file gives that pattern
an implementation-independent trace semantics.

A frame is recognized locally: its first cycle satisfies `isFirst`, and no
later cycle in the same frame window does.  A second marker arriving too soon
therefore invalidates the earlier candidate frame.  It may still begin a new
frame of its own when the trace contains a complete, uninterrupted window
after it.
-/

/-- A fixed-length sequence represented by its natural finite index. -/
abbrev Frame (length : Nat) (α : Type u) := Fin length → α

/-- Read a complete fixed-length window from a finite sequence. -/
def window {α : Type u} {length : Nat} (values : List α) (start : Nat)
    (within : start + length ≤ values.length) : Frame length α :=
  fun offset => values.get ⟨start + offset.val, by omega⟩

@[simp] theorem window_apply {α : Type u} {length : Nat}
    (values : List α) (start : Nat)
    (within : start + length ≤ values.length) (offset : Fin length) :
    window values start within offset =
      values.get ⟨start + offset.val, by omega⟩ :=
  rfl

/-- A window depends on its numerical start and source sequence, not on the
particular proof that the complete window is present. -/
theorem window_congr {α : Type u} {length : Nat} {values : List α}
    {firstStart secondStart : Nat}
    {firstWithin : firstStart + length ≤ values.length}
    {secondWithin : secondStart + length ≤ values.length}
    (equal : firstStart = secondStart) :
    window values firstStart firstWithin =
      window values secondStart secondWithin := by
  subst secondStart
  rfl

/-- Mapping a complete sequence and then taking a frame window is the same as
mapping the extracted frame. -/
theorem window_map {α : Type u} {β : Type v} {length : Nat}
    (function : α → β) (values : List α) (start : Nat)
    (mappedWithin : start + length ≤ (values.map function).length)
    (within : start + length ≤ values.length) :
    window (values.map function) start mappedWithin =
      fun offset => function (window values start within offset) := by
  funext offset
  simp [window]

/-- A frame begins with a marker and contains no later marker. -/
def Starts {α : Type u} {length : Nat} (positive : 0 < length)
    (isFirst : α → Prop) (frame : Frame length α) : Prop :=
  isFirst (frame ⟨0, positive⟩) ∧
    ∀ offset : Fin length, offset.val ≠ 0 → ¬ isFirst (frame offset)

theorem Starts.first {α : Type u} {length : Nat} {positive : 0 < length}
    {isFirst : α → Prop} {frame : Frame length α}
    (starts : Starts positive isFirst frame) :
    isFirst (frame ⟨0, positive⟩) :=
  starts.1

theorem Starts.not_first {α : Type u} {length : Nat}
    {positive : 0 < length} {isFirst : α → Prop}
    {frame : Frame length α} (starts : Starts positive isFirst frame)
    (offset : Fin length) (nonzero : offset.val ≠ 0) :
    ¬ isFirst (frame offset) :=
  starts.2 offset nonzero

/-- A marker in the interior of a candidate frame invalidates that candidate.
This is deliberately local: it says nothing about whether the newer marker
begins another valid frame. -/
theorem not_starts_of_early_marker
    {α : Type u} {length : Nat} {positive : 0 < length}
    {isFirst : α → Prop} {frame : Frame length α}
    (offset : Fin length) (nonzero : offset.val ≠ 0)
    (marked : isFirst (frame offset)) :
    ¬ Starts positive isFirst frame := by
  intro starts
  exact starts.not_first offset nonzero marked

/-- Relational composition at the level of complete frames. -/
def Comp {length : Nat} {α : Type u} {β : Type v} {γ : Type w}
    (left : Frame length α → Frame length β → Prop)
    (right : Frame length β → Frame length γ → Prop)
    (input : Frame length α) (output : Frame length γ) : Prop :=
  ∃ intermediate, left input intermediate ∧ right intermediate output

/-- Equal-length streams related frame-by-frame after a fixed displacement.

The implication is intentional.  Only a complete input window beginning with
one marker and containing no subsequent marker is specified.  Truncated
windows, unmarked traffic, and candidates interrupted by an early marker do
not constrain the corresponding output window. -/
def Relates {α : Type u} {β : Type v} (frameLength latency : Nat)
    (positive : 0 < frameLength)
    (inputFirst : α → Prop) (outputFirst : β → Prop)
    (relation : Frame frameLength α → Frame frameLength β → Prop)
    (inputs : List α) (outputs : List β) : Prop :=
  outputs.length = inputs.length ∧
    ∀ (start : Nat)
        (inputWithin : start + frameLength ≤ inputs.length)
        (outputWithin : start + latency + frameLength ≤ outputs.length),
      Starts positive inputFirst (window inputs start inputWithin) →
        Starts positive outputFirst
            (window outputs (start + latency) (by omega)) ∧
          relation (window inputs start inputWithin)
            (window outputs (start + latency) (by omega))

/-- Apply a framed relation to the observable boundary trace of a module. -/
def Holds {ports : ModulePorts} (frameLength latency : Nat)
    (positive : 0 < frameLength)
    (inputFirst : ports.inputs.Values → Prop)
    (outputFirst : ports.outputs.Values → Prop)
    (relation : Frame frameLength ports.inputs.Values →
      Frame frameLength ports.outputs.Values → Prop)
    (trace : BoundaryTrace ports) : Prop :=
  Relates frameLength latency positive inputFirst outputFirst relation
    trace.inputs trace.outputs

/-- Project a port-record framed contract onto ordinary carried values.  This
is the standard bridge used to compose neighboring modules whose input and
output port labels differ even though the values wired between them agree. -/
theorem relates_of_holds_projection
    {ports : ModulePorts} {frameLength latency : Nat}
    {positive : 0 < frameLength} {α : Type u} {β : Type v}
    {inputFirst : α → Prop} {outputFirst : β → Prop}
    {relation : Frame frameLength α → Frame frameLength β → Prop}
    {trace : BoundaryTrace ports}
    (inputProjection : ports.inputs.Values → α)
    (outputProjection : ports.outputs.Values → β)
    (holds : Holds frameLength latency positive
      (fun input => inputFirst (inputProjection input))
      (fun output => outputFirst (outputProjection output))
      (fun input output =>
        relation (fun cycle => inputProjection (input cycle))
          (fun cycle => outputProjection (output cycle))) trace) :
    Relates frameLength latency positive inputFirst outputFirst relation
      (trace.inputs.map inputProjection)
      (trace.outputs.map outputProjection) := by
  unfold Holds at holds
  unfold Relates at holds ⊢
  constructor
  · simpa only [List.length_map] using holds.1
  · intro start inputWithin outputWithin starts
    have originalInputWithin :
        start + frameLength ≤ trace.inputs.length := by
      simpa using inputWithin
    have originalOutputWithin :
        start + latency + frameLength ≤ trace.outputs.length := by
      simpa using outputWithin
    have originalStarts :
        Starts positive (fun input => inputFirst (inputProjection input))
          (window trace.inputs start originalInputWithin) := by
      simpa only [Starts,
        window_map inputProjection trace.inputs start inputWithin
        originalInputWithin] using starts
    have observed := holds.2 start originalInputWithin
      originalOutputWithin originalStarts
    simpa only [Starts,
      window_map inputProjection trace.inputs start inputWithin
        originalInputWithin,
      window_map outputProjection trace.outputs (start + latency)
        (by omega : start + latency + frameLength ≤
          (trace.outputs.map outputProjection).length)
        (by omega : start + latency + frameLength ≤ trace.outputs.length)]
      using observed

/-- Reassemble a port-record framed contract from a relation on projected
observations.  Together with `relates_of_holds_projection`, this makes the
projection bridge usable in both directions during structural composition. -/
theorem holds_of_relates_projection
    {ports : ModulePorts} {frameLength latency : Nat}
    {positive : 0 < frameLength} {α : Type u} {β : Type v}
    {inputFirst : α → Prop} {outputFirst : β → Prop}
    {relation : Frame frameLength α → Frame frameLength β → Prop}
    {trace : BoundaryTrace ports}
    (inputProjection : ports.inputs.Values → α)
    (outputProjection : ports.outputs.Values → β)
    (relates : Relates frameLength latency positive inputFirst outputFirst
      relation (trace.inputs.map inputProjection)
      (trace.outputs.map outputProjection)) :
    Holds frameLength latency positive
      (fun input => inputFirst (inputProjection input))
      (fun output => outputFirst (outputProjection output))
      (fun input output =>
        relation (fun cycle => inputProjection (input cycle))
          (fun cycle => outputProjection (output cycle))) trace := by
  unfold Holds
  unfold Relates at relates ⊢
  constructor
  · simpa only [List.length_map] using relates.1
  · intro start inputWithin outputWithin starts
    have mappedInputWithin :
        start + frameLength ≤ (trace.inputs.map inputProjection).length := by
      simpa using inputWithin
    have mappedOutputWithin :
        start + latency + frameLength ≤
          (trace.outputs.map outputProjection).length := by
      simpa using outputWithin
    have mappedStarts :
        Starts positive inputFirst
          (window (trace.inputs.map inputProjection) start
            mappedInputWithin) := by
      simpa only [Starts,
        window_map inputProjection trace.inputs start mappedInputWithin
          inputWithin] using starts
    have observed := relates.2 start mappedInputWithin mappedOutputWithin
      mappedStarts
    simpa only [Starts,
      window_map inputProjection trace.inputs start mappedInputWithin
        inputWithin,
      window_map outputProjection trace.outputs (start + latency)
        (by omega : start + latency + frameLength ≤
          (trace.outputs.map outputProjection).length)
        (by omega : start + latency + frameLength ≤ trace.outputs.length)]
      using observed

/-- Read the guarantee for one complete, valid input frame. -/
theorem relation_at
    {α : Type u} {β : Type v} {frameLength latency : Nat}
    {positive : 0 < frameLength}
    {inputFirst : α → Prop} {outputFirst : β → Prop}
    {relation : Frame frameLength α → Frame frameLength β → Prop}
    {inputs : List α} {outputs : List β}
    (relates : Relates frameLength latency positive inputFirst outputFirst
      relation inputs outputs)
    (start : Nat)
    (inputWithin : start + frameLength ≤ inputs.length)
    (outputWithin : start + latency + frameLength ≤ outputs.length)
    (starts : Starts positive inputFirst
      (window inputs start inputWithin)) :
    Starts positive outputFirst
        (window outputs (start + latency) (by omega)) ∧
      relation (window inputs start inputWithin)
        (window outputs (start + latency) (by omega)) :=
  relates.2 start inputWithin outputWithin starts

/-- Weaken the carried frame relation without changing latency or marker
semantics. -/
theorem mono
    {α : Type u} {β : Type v} {frameLength latency : Nat}
    {positive : 0 < frameLength}
    {inputFirst : α → Prop} {outputFirst : β → Prop}
    {strong weak : Frame frameLength α → Frame frameLength β → Prop}
    {inputs : List α} {outputs : List β}
    (relates : Relates frameLength latency positive inputFirst outputFirst
      strong inputs outputs)
    (implies : ∀ input output, strong input output → weak input output) :
    Relates frameLength latency positive inputFirst outputFirst
      weak inputs outputs := by
  refine ⟨relates.1, ?_⟩
  intro start inputWithin outputWithin starts
  have observed := relates.2 start inputWithin outputWithin starts
  exact ⟨observed.1, implies _ _ observed.2⟩

/-- Serial composition of framed stages adds their latencies.  The first
stage's output marker supplies exactly the valid input-frame premise needed by
the second stage. -/
theorem serial
    {α : Type u} {β : Type v} {γ : Type w}
    {frameLength leftLatency rightLatency : Nat}
    {positive : 0 < frameLength}
    {inputFirst : α → Prop} {middleFirst : β → Prop}
    {outputFirst : γ → Prop}
    {leftRelation : Frame frameLength α → Frame frameLength β → Prop}
    {rightRelation : Frame frameLength β → Frame frameLength γ → Prop}
    {inputs : List α} {intermediate : List β} {outputs : List γ}
    (left : Relates frameLength leftLatency positive inputFirst middleFirst
      leftRelation inputs intermediate)
    (right : Relates frameLength rightLatency positive middleFirst outputFirst
      rightRelation intermediate outputs) :
    Relates frameLength (leftLatency + rightLatency) positive
      inputFirst outputFirst (Comp leftRelation rightRelation) inputs outputs := by
  constructor
  · exact right.1.trans left.1
  · intro start inputWithin outputWithin inputStarts
    have middleWithin :
        start + leftLatency + frameLength ≤ intermediate.length := by
      rw [← right.1]
      omega
    have leftResult := left.2 start inputWithin middleWithin inputStarts
    have rightOutputWithin :
        (start + leftLatency) + rightLatency + frameLength ≤ outputs.length := by
      omega
    have rightResult := right.2 (start + leftLatency) middleWithin
      rightOutputWithin leftResult.1
    have outputWindowEqual :
        window outputs ((start + leftLatency) + rightLatency)
            rightOutputWithin =
          window outputs (start + (leftLatency + rightLatency))
            outputWithin :=
      window_congr (Nat.add_assoc start leftLatency rightLatency)
    constructor
    · rw [← outputWindowEqual]
      exact rightResult.1
    · refine ⟨window intermediate (start + leftLatency) middleWithin,
        leftResult.2, ?_⟩
      rw [← outputWindowEqual]
      exact rightResult.2

/-- A deterministic specialization of a framed relation. -/
def Computes {α : Type u} {β : Type v} (frameLength latency : Nat)
    (positive : 0 < frameLength)
    (inputFirst : α → Prop) (outputFirst : β → Prop)
    (function : Frame frameLength α → Frame frameLength β)
    (inputs : List α) (outputs : List β) : Prop :=
  Relates frameLength latency positive inputFirst outputFirst
    (fun input output => output = function input) inputs outputs

/-- Deterministic framed computations compose by ordinary function
composition. -/
theorem computes_serial
    {α : Type u} {β : Type v} {γ : Type w}
    {frameLength leftLatency rightLatency : Nat}
    {positive : 0 < frameLength}
    {inputFirst : α → Prop} {middleFirst : β → Prop}
    {outputFirst : γ → Prop}
    {leftFunction : Frame frameLength α → Frame frameLength β}
    {rightFunction : Frame frameLength β → Frame frameLength γ}
    {inputs : List α} {intermediate : List β} {outputs : List γ}
    (left : Computes frameLength leftLatency positive inputFirst middleFirst
      leftFunction inputs intermediate)
    (right : Computes frameLength rightLatency positive middleFirst outputFirst
      rightFunction intermediate outputs) :
    Computes frameLength (leftLatency + rightLatency) positive
      inputFirst outputFirst (rightFunction ∘ leftFunction) inputs outputs := by
  have composed := serial left right
  refine ⟨composed.1, ?_⟩
  intro start inputWithin outputWithin starts
  have result := composed.2 start inputWithin outputWithin starts
  refine ⟨result.1, ?_⟩
  rcases result.2 with ⟨middle, leftEqual, rightEqual⟩
  subst middle
  simpa only [Function.comp_apply] using rightEqual

/-- The unchanged sequence computes the identity function with zero latency. -/
theorem computes_id
    {α : Type u} {frameLength : Nat} {positive : 0 < frameLength}
    {isFirst : α → Prop} (values : List α) :
    Computes frameLength 0 positive isFirst isFirst id values values := by
  constructor
  · rfl
  · intro start inputWithin outputWithin starts
    have windowsEqual :
        window values (start + 0) outputWithin =
          window values start inputWithin :=
      window_congr (by omega)
    constructor
    · rw [windowsEqual]
      exact starts
    · simp only [id, windowsEqual]

/-- Re-express a framed computation whose input sequence was produced by a
pointwise map.  Frame extraction commutes with that map, so the deterministic
frame function receives the mapped input frame. -/
theorem computes_map_inputs
    {α : Type u} {β : Type v} {γ : Type w}
    {frameLength latency : Nat} {positive : 0 < frameLength}
    {inputFirst : β → Prop} {outputFirst : γ → Prop}
    {function : Frame frameLength β → Frame frameLength γ}
    {inputs : List α} {outputs : List γ}
    (mapInput : α → β)
    (holds : Computes frameLength latency positive inputFirst outputFirst
      function (inputs.map mapInput) outputs) :
    Computes frameLength latency positive
      (fun input => inputFirst (mapInput input)) outputFirst
      (fun frame => function (fun index => mapInput (frame index)))
      inputs outputs := by
  constructor
  · simpa only [List.length_map] using holds.1
  · intro start inputWithin outputWithin starts
    have mappedInputWithin :
        start + frameLength ≤ (inputs.map mapInput).length := by
      simpa using inputWithin
    have mappedStarts :
        Starts positive inputFirst
          (window (inputs.map mapInput) start mappedInputWithin) := by
      simpa only [Starts,
        window_map mapInput inputs start mappedInputWithin inputWithin] using
        starts
    have observed := holds.2 start mappedInputWithin outputWithin mappedStarts
    refine ⟨observed.1, ?_⟩
    simpa only [window_map mapInput inputs start mappedInputWithin inputWithin]
      using observed.2

/-- Map every value of a framed computation's output sequence.  The supplied
marker equivalence records that the map preserves exactly the output markers
used to recognize valid frames. -/
theorem computes_map_outputs
    {α : Type u} {β : Type v} {γ : Type w}
    {frameLength latency : Nat} {positive : 0 < frameLength}
    {inputFirst : α → Prop} {outputFirst : β → Prop}
    {mappedOutputFirst : γ → Prop}
    {function : Frame frameLength α → Frame frameLength β}
    {inputs : List α} {outputs : List β}
    (mapOutput : β → γ)
    (preservesFirst : ∀ output,
      mappedOutputFirst (mapOutput output) ↔ outputFirst output)
    (holds : Computes frameLength latency positive inputFirst outputFirst
      function inputs outputs) :
    Computes frameLength latency positive inputFirst mappedOutputFirst
      (fun frame index => mapOutput (function frame index))
      inputs (outputs.map mapOutput) := by
  constructor
  · simpa only [List.length_map] using holds.1
  · intro start inputWithin outputWithin starts
    have originalOutputWithin :
        start + latency + frameLength ≤ outputs.length := by
      simpa using outputWithin
    have observed := holds.2 start inputWithin originalOutputWithin starts
    have mappedStarts :
        Starts positive mappedOutputFirst
          (window (outputs.map mapOutput) (start + latency)
            outputWithin) := by
      simpa only [Starts, preservesFirst,
        window_map mapOutput outputs (start + latency) outputWithin
          originalOutputWithin] using observed.1
    refine ⟨mappedStarts, ?_⟩
    funext index
    have pointwise := congrArg mapOutput (congrFun observed.2 index)
    simpa only [window_map mapOutput outputs (start + latency) outputWithin
      originalOutputWithin] using pointwise

/-- A payload computation and an independent marker delay with the same
latency form one deterministic framed computation.  This is the standard
composition rule for a data path accompanied by a separate shift register
carrying its frame marker. -/
theorem computes_of_components
    {dataIn dataOut : Type}
    {frameLength latency : Nat} {positive : 0 < frameLength}
    {function : dataIn → dataOut}
    {inputs : List (Bool × dataIn)} {outputs : List (Bool × dataOut)}
    (marker : FixedLatency.Computes latency id
      (inputs.map (fun value => value.1))
      (outputs.map (fun value => value.1)))
    (payload : FixedLatency.Computes latency function
      (inputs.map (fun value => value.2))
      (outputs.map (fun value => value.2))) :
    Computes frameLength latency positive
      (fun input => input.1 = true) (fun output => output.1 = true)
      (fun frame cycle => ((frame cycle).1, function (frame cycle).2))
      inputs outputs := by
  constructor
  · simpa only [List.length_map] using marker.1
  · intro start inputWithin outputWithin inputStarts
    have markerAt (offset : Fin frameLength) :
        (window outputs (start + latency) (by omega) offset).1 =
          (window inputs start inputWithin offset).1 := by
      have inputInTrace :
          start + offset.val < (inputs.map (fun value => value.1)).length := by
        simp only [List.length_map]
        omega
      have outputInTrace :
          (start + offset.val) + latency <
            (outputs.map (fun value => value.1)).length := by
        simp only [List.length_map]
        omega
      have delayed := marker.2 (start + offset.val) inputInTrace outputInTrace
      simpa [id, List.get_eq_getElem, List.getElem_map,
        window_apply, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        delayed
    have payloadAt (offset : Fin frameLength) :
        (window outputs (start + latency) (by omega) offset).2 =
          function (window inputs start inputWithin offset).2 := by
      have inputInTrace :
          start + offset.val < (inputs.map (fun value => value.2)).length := by
        simp only [List.length_map]
        omega
      have outputInTrace :
          (start + offset.val) + latency <
            (outputs.map (fun value => value.2)).length := by
        simp only [List.length_map]
        omega
      have delayed := payload.2 (start + offset.val)
        inputInTrace outputInTrace
      simpa only [List.get_eq_getElem, List.getElem_map, window_apply,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using delayed
    constructor
    · constructor
      · change (window outputs (start + latency) (by omega)
            ⟨0, positive⟩).1 = true
        rw [markerAt]
        exact inputStarts.first
      · intro offset nonzero
        change ¬(window outputs (start + latency) (by omega) offset).1 = true
        intro marked
        apply inputStarts.not_first offset nonzero
        change (window inputs start inputWithin offset).1 = true
        rw [← markerAt offset]
        exact marked
    · funext offset
      apply Prod.ext
      · exact markerAt offset
      · exact payloadAt offset

/-- A framed relation that specifies only the payload is deterministic on the
whole `(marker, payload)` frame: `Starts` already fixes the marker to `true`
at offset zero and `false` everywhere else. -/
theorem computes_of_payload_relation
    {dataIn dataOut : Type}
    {frameLength latency : Nat} {positive : 0 < frameLength}
    {function : Frame frameLength dataIn → Frame frameLength dataOut}
    {inputs : List (Bool × dataIn)} {outputs : List (Bool × dataOut)}
    (relates : Relates frameLength latency positive
      (fun input => input.1 = true) (fun output => output.1 = true)
      (fun input output =>
        (fun cycle => (output cycle).2) =
          function (fun cycle => (input cycle).2)) inputs outputs) :
    Computes frameLength latency positive
      (fun input => input.1 = true) (fun output => output.1 = true)
      (fun frame cycle => ((frame cycle).1,
        function (fun index => (frame index).2) cycle)) inputs outputs := by
  constructor
  · exact relates.1
  · intro start inputWithin outputWithin inputStarts
    have observed := relates.2 start inputWithin outputWithin inputStarts
    rcases observed with ⟨outputStarts, payloadEqual⟩
    refine ⟨outputStarts, ?_⟩
    funext offset
    apply Prod.ext
    · by_cases zero : offset.val = 0
      · have offsetEqual : offset = ⟨0, positive⟩ := by
          apply Fin.ext
          exact zero
        subst offset
        exact outputStarts.first.trans inputStarts.first.symm
      · have inputNot := inputStarts.not_first offset zero
        have outputNot := outputStarts.not_first offset zero
        cases inputMarker : (window inputs start inputWithin offset).1 <;>
          cases outputMarker :
            (window outputs (start + latency) (by omega) offset).1 <;>
          simp_all
    · exact congrFun payloadEqual offset

end Silean.FramedLatency
