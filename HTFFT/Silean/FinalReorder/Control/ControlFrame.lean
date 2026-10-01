import HTFFT.Silean.FinalReorder.Control.ControlAddress
import Silean.Semantics.FramedLatency

/-! Complete-frame consequences of the natural final-reorder controller. -/

namespace HTFFT.Silean.FinalReorder.Control

open _root_.Silean

@[ext] structure WriteObservation (addressWidth : Nat) where
  address0 : Address addressWidth
  address1 : Address addressWidth
  swap : Bool
  bypass : Bool

@[ext] structure ReadObservation (addressWidth : Nat) where
  address : Address addressWidth
  swap : Bool

def writeControls (addressWidth : Nat) (address : Address addressWidth) :
    WriteObservation addressWidth where
  address0 := writeAddress0 addressWidth address
  address1 := writeAddress1 addressWidth address
  swap := writeSwap addressWidth address
  bypass := bypass addressWidth address

def readControls (addressWidth : Nat) (address : Address addressWidth) :
    ReadObservation addressWidth where
  address := readAddress addressWidth address
  swap := readSwap addressWidth address

def writeObservation (addressWidth : Nat)
    (output : (ports addressWidth).outputs.Values) :
    WriteObservation addressWidth where
  address0 := output .o_writeAddress0
  address1 := output .o_writeAddress1
  swap := output .o_writeSwap
  bypass := output .o_bypass

def readObservation (addressWidth : Nat)
    (output : (ports addressWidth).outputs.Values) :
    ReadObservation addressWidth where
  address := output .o_readAddress
  swap := output .o_readSwap

/-- Pure marker-driven address counter. -/
def run : Address addressWidth → List Bool →
    List (Address addressWidth) × Address addressWidth
  | state, [] => ([], state)
  | state, first :: rest =>
      let address := effectiveAddress addressWidth first state
      let tail := run
        (_root_.Silean.Modules.Increment.incrementValue addressWidth address)
        rest
      (address :: tail.1, tail.2)

@[simp] theorem run_append (addressWidth : Nat)
    (state : Address addressWidth) (left right : List Bool) :
    run state (left ++ right) =
      let middle := run state left
      let suffix := run middle.2 right
      (middle.1 ++ suffix.1, suffix.2) := by
  induction left generalizing state with
  | nil => rfl
  | cons first left induction =>
      simp only [List.cons_append, run]
      rw [induction]

@[simp] theorem run_observations_length (addressWidth : Nat)
    (state : Address addressWidth) (markers : List Bool) :
    (run state markers).1.length = markers.length := by
  induction markers generalizing state with
  | nil => rfl
  | cons first markers induction => simp [run, induction]

def expectedAddresses (addressWidth start count : Nat) :
    List (Address addressWidth) :=
  (List.range' start count).map (BitVector.ofNat addressWidth)

theorem run_false_traversal (addressWidth start count : Nat)
    (stateInRange : start < BitVector.cardinality addressWidth)
    (completes : start + count = BitVector.cardinality addressWidth) :
    run (addressWidth := addressWidth) (BitVector.ofNat addressWidth start)
        (List.replicate count false) =
      (expectedAddresses addressWidth start count,
        zeroAddress addressWidth) := by
  induction count generalizing start with
  | zero => omega
  | succ count induction =>
      by_cases tailEmpty : count = 0
      · subst count
        have startLast : start = BitVector.cardinality addressWidth - 1 := by
          omega
        subst start
        simp only [List.replicate_succ, List.replicate_zero, run,
          expectedAddresses, Prod.mk.injEq]
        constructor
        · simp [effectiveAddress]
        · exact increment_ofNat_cardinality_sub_one addressWidth
      · have nextInRange : start + 1 <
            BitVector.cardinality addressWidth := by omega
        have tailCompletes : start + 1 + count =
            BitVector.cardinality addressWidth := by omega
        simp only [List.replicate_succ, run, effectiveAddress,
          Bool.cond_false]
        rw [increment_ofNat addressWidth start nextInRange,
          induction (start + 1) nextInRange tailCompletes]
        rfl

theorem run_marked_frame (addressWidth : Nat) (positive : 0 < addressWidth)
    (initial : Address addressWidth) :
    run (addressWidth := addressWidth) initial
        (true :: List.replicate
          (BitVector.cardinality addressWidth - 1) false) =
      (expectedAddresses addressWidth 0
          (BitVector.cardinality addressWidth),
        zeroAddress addressWidth) := by
  have cardTwo : 2 ≤ BitVector.cardinality addressWidth := by
    rw [BitVector.cardinality_eq_pow]
    exact Nat.one_lt_two_pow (Nat.ne_of_gt positive)
  have tail := run_false_traversal addressWidth 1
    (BitVector.cardinality addressWidth - 1) (by omega) (by omega)
  have tail' : run (oneAddress addressWidth)
      (List.replicate (BitVector.cardinality addressWidth - 1) false) =
    (expectedAddresses addressWidth 1
      (BitVector.cardinality addressWidth - 1), zeroAddress addressWidth) := by
    simpa [oneAddress] using tail
  simp only [run, effectiveAddress, Bool.cond_true,
    increment_zeroAddress]
  rw [tail']
  apply Prod.ext
  · unfold expectedAddresses
    rw [show BitVector.cardinality addressWidth =
      (BitVector.cardinality addressWidth - 1) + 1 by omega]
    rw [List.range'_succ]
    simp [zeroAddress]
  · rfl

/-- During fewer than one complete traversal, marker resets can only reduce
the counter relative to ordinary counting. -/
theorem run_short_final (addressWidth start : Nat)
    (positive : 0 < addressWidth) (markers : List Bool)
    (short : start + markers.length < BitVector.cardinality addressWidth) :
    ∃ finalValue : Nat,
      finalValue ≤ start + markers.length ∧
      (run (addressWidth := addressWidth)
        (BitVector.ofNat addressWidth start) markers).2 =
          BitVector.ofNat addressWidth finalValue := by
  induction markers generalizing start with
  | nil => exact ⟨start, by simp, rfl⟩
  | cons first markers induction =>
      simp only [List.length_cons] at short
      cases first with
      | false =>
          have nextInRange : start + 1 <
              BitVector.cardinality addressWidth := by omega
          have tailShort : start + 1 + markers.length <
              BitVector.cardinality addressWidth := by omega
          simp only [run, effectiveAddress, Bool.cond_false]
          rw [increment_ofNat addressWidth start nextInRange]
          obtain ⟨finalValue, bound, final⟩ :=
            induction (start + 1) tailShort
          exact ⟨finalValue, by simp only [List.length_cons]; omega, final⟩
      | true =>
          have cardTwo : 2 ≤ BitVector.cardinality addressWidth := by
            rw [BitVector.cardinality_eq_pow]
            exact Nat.one_lt_two_pow (Nat.ne_of_gt positive)
          have tailShort : 1 + markers.length <
              BitVector.cardinality addressWidth := by omega
          simp only [run, effectiveAddress, Bool.cond_true,
            increment_zeroAddress]
          obtain ⟨finalValue, bound, final⟩ := induction 1 tailShort
          exact ⟨finalValue, by simp only [List.length_cons]; omega, final⟩

/-- Observation `position` in a pure counter run is computed from the state
reached after the preceding prefix. -/
theorem run_get_eq_effectiveAddress_after (addressWidth : Nat)
    (state : Address addressWidth) (markers : List Bool)
    (position : Nat) (occurs : position < markers.length) :
    (run state markers).1.get ⟨position, by
      simpa [run_observations_length addressWidth state markers] using occurs⟩ =
      effectiveAddress addressWidth (markers.get ⟨position, occurs⟩)
        (run state (markers.take position)).2 := by
  induction position generalizing state markers with
  | zero =>
      cases markers with
      | nil => simp at occurs
      | cons first markers => rfl
  | succ position induction =>
      cases markers with
      | nil => simp at occurs
      | cons first markers =>
          have tailOccurs : position < markers.length := by simpa using occurs
          simpa [run, List.take_succ_cons] using induction
            (_root_.Silean.Modules.Increment.incrementValue addressWidth
              (effectiveAddress addressWidth first state))
            markers tailOccurs

/-- At continuation offset `position`, the effective counter is some natural
value no greater than `position`, even if a later frame marker restarted it. -/
theorem run_short_observation (addressWidth : Nat)
    (positive : 0 < addressWidth) (markers : List Bool)
    (position : Nat) (occurs : position < markers.length)
    (short : position < BitVector.cardinality addressWidth) :
    ∃ value : Nat, value ≤ position ∧
      (run (addressWidth := addressWidth) (zeroAddress addressWidth) markers).1.get
        ⟨position, by rw [run_observations_length]; exact occurs⟩ =
          BitVector.ofNat addressWidth value := by
  rw [run_get_eq_effectiveAddress_after addressWidth
    (zeroAddress addressWidth) markers position occurs]
  have prefixLength : (markers.take position).length = position := by
    simp
    omega
  have zeroIsOfNat : zeroAddress addressWidth =
      BitVector.ofNat addressWidth 0 := rfl
  rw [zeroIsOfNat]
  obtain ⟨currentValue, bound, current⟩ := run_short_final
    addressWidth 0 positive (markers.take position) (by
      rw [prefixLength]
      simpa using short)
  have currentBound : currentValue ≤ position := by
    rw [prefixLength] at bound
    simpa using bound
  rw [current]
  cases marker : markers.get ⟨position, occurs⟩
  · exact ⟨currentValue, currentBound, by
      simp [effectiveAddress]⟩
  · exact ⟨0, Nat.zero_le _, by
      simp [effectiveAddress, zeroAddress]⟩

/-- A controller trace projects to the pure write-counter run. -/
theorem write_observations_of_trace
    {initial final : State addressWidth}
    {inputs : List (ports addressWidth).inputs.Values}
    {outputs : List (ports addressWidth).outputs.Values}
    (trace : Trace (Transition addressWidth) initial inputs outputs final) :
    (outputs.map (writeObservation addressWidth), final.storedWriteAddress) =
      let result := run initial.storedWriteAddress
        (inputs.map fun input => (show Bool from input .i_first))
      (result.1.map (writeControls addressWidth), result.2) := by
  induction trace with
  | nil state => rfl
  | @cons currentState nextState finalState remainingInputs remainingOutputs
      input output step rest induction =>
      rcases step with ⟨outputEqual, nextEqual⟩
      subst nextEqual
      rcases outputEqual with ⟨address0, address1, _, swap, _, bypassEq⟩
      dsimp only [nextState] at induction
      simp only [List.map_cons, run]
      have observationsEqual := congrArg Prod.fst induction
      have finalEqual := congrArg Prod.snd induction
      have observationsEqual' := show
        List.map (writeObservation addressWidth) remainingOutputs = _ from
          observationsEqual
      have finalEqual' := show finalState.storedWriteAddress = _ from
        finalEqual
      rw [observationsEqual', finalEqual']
      have headEqual : writeObservation addressWidth output =
          writeControls addressWidth
            (effectiveAddress addressWidth (input .i_first)
              currentState.storedWriteAddress) := by
        apply WriteObservation.ext <;> assumption
      rw [headEqual]

/-- A controller trace projects independently to the pure read-counter run. -/
theorem read_observations_of_trace
    {initial final : State addressWidth}
    {inputs : List (ports addressWidth).inputs.Values}
    {outputs : List (ports addressWidth).outputs.Values}
    (trace : Trace (Transition addressWidth) initial inputs outputs final) :
    (outputs.map (readObservation addressWidth), final.storedReadAddress) =
      let result := run initial.storedReadAddress
        (inputs.map fun input => (show Bool from input .i_readFirst))
      (result.1.map (readControls addressWidth), result.2) := by
  induction trace with
  | nil state => rfl
  | @cons currentState nextState finalState remainingInputs remainingOutputs
      input output step rest induction =>
      rcases step with ⟨outputEqual, nextEqual⟩
      subst nextEqual
      rcases outputEqual with ⟨_, _, address, _, swap, _⟩
      dsimp only [nextState] at induction
      simp only [List.map_cons, run]
      have observationsEqual := congrArg Prod.fst induction
      have finalEqual := congrArg Prod.snd induction
      have observationsEqual' := show
        List.map (readObservation addressWidth) remainingOutputs = _ from
          observationsEqual
      have finalEqual' := show finalState.storedReadAddress = _ from
        finalEqual
      rw [observationsEqual', finalEqual']
      have headEqual : readObservation addressWidth output =
          readControls addressWidth
            (effectiveAddress addressWidth (input .i_readFirst)
              currentState.storedReadAddress) := by
        apply ReadObservation.ext <;> assumption
      rw [headEqual]

private theorem markerList_of_starts
    {Value : Type} {length : Nat} (positive : 0 < length)
    (marker : Value → Bool) (values : List Value) (start : Nat)
    (within : start + length ≤ values.length)
    (starts : FramedLatency.Starts positive
      (fun value => marker value = true)
      (FramedLatency.window values start within)) :
    (List.ofFn (FramedLatency.window values start within)).map marker =
      true :: List.replicate (length - 1) false := by
  apply List.ext_getElem
  · simp
    omega
  · intro index leftIn rightIn
    simp only [List.getElem_map, List.getElem_ofFn] at leftIn ⊢
    have indexIn : index < length := by simpa using leftIn
    cases index with
    | zero => exact starts.first
    | succ index =>
      have unmarked := starts.not_first ⟨index + 1, indexIn⟩
        (Nat.succ_ne_zero index)
      have equalFalse : marker
          (FramedLatency.window values start within
            ⟨index + 1, indexIn⟩) = false := by
        cases equal : marker
            (FramedLatency.window values start within
              ⟨index + 1, indexIn⟩)
        · rfl
        · exact False.elim (unmarked equal)
      simpa only [List.getElem_cons_succ, List.getElem_replicate]
        using equalFalse

theorem write_observations_of_marked_window
    {initial final : State addressWidth}
    {inputs : List (ports addressWidth).inputs.Values}
    {outputs : List (ports addressWidth).outputs.Values}
    (positive : 0 < addressWidth)
    (trace : Trace (Transition addressWidth) initial inputs outputs final)
    (start : Nat)
    (within : start + BitVector.cardinality addressWidth ≤ inputs.length)
    (starts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos addressWidth)
      (fun input : (ports addressWidth).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window inputs start within)) :
    (List.ofFn (FramedLatency.window outputs start (by
      rw [trace.length_eq]
      exact within))).map (writeObservation addressWidth) =
      (expectedAddresses addressWidth 0
        (BitVector.cardinality addressWidth)).map
          (writeControls addressWidth) := by
  obtain ⟨windowInitial, windowFinal, windowTrace⟩ :=
    FramedLatency.exists_trace_window trace start
      (BitVector.cardinality addressWidth) within
  have markers := markerList_of_starts
    (by
      rw [BitVector.cardinality_eq_pow]
      exact Nat.two_pow_pos addressWidth)
    (fun input : (ports addressWidth).inputs.Values => input .i_first)
    inputs start within starts
  have projected := write_observations_of_trace windowTrace
  have runEqual := run_marked_frame addressWidth positive
    windowInitial.storedWriteAddress
  have lists := congrArg Prod.fst projected
  rw [markers, runEqual] at lists
  exact lists

theorem read_observations_of_marked_window
    {initial final : State addressWidth}
    {inputs : List (ports addressWidth).inputs.Values}
    {outputs : List (ports addressWidth).outputs.Values}
    (positive : 0 < addressWidth)
    (trace : Trace (Transition addressWidth) initial inputs outputs final)
    (start : Nat)
    (within : start + BitVector.cardinality addressWidth ≤ inputs.length)
    (starts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos addressWidth)
      (fun input : (ports addressWidth).inputs.Values =>
        (show Bool from input .i_readFirst) = true)
      (FramedLatency.window inputs start within)) :
    (List.ofFn (FramedLatency.window outputs start (by
      rw [trace.length_eq]
      exact within))).map (readObservation addressWidth) =
      (expectedAddresses addressWidth 0
        (BitVector.cardinality addressWidth)).map
          (readControls addressWidth) := by
  obtain ⟨windowInitial, windowFinal, windowTrace⟩ :=
    FramedLatency.exists_trace_window trace start
      (BitVector.cardinality addressWidth) within
  have markers := markerList_of_starts
    (by
      rw [BitVector.cardinality_eq_pow]
      exact Nat.two_pow_pos addressWidth)
    (fun input : (ports addressWidth).inputs.Values => input .i_readFirst)
    inputs start within starts
  have projected := read_observations_of_trace windowTrace
  have runEqual := run_marked_frame addressWidth positive
    windowInitial.storedReadAddress
  have lists := congrArg Prod.fst projected
  rw [markers, runEqual] at lists
  exact lists

theorem write_observation_at_of_marked_window
    {initial final : State addressWidth}
    {inputs : List (ports addressWidth).inputs.Values}
    {outputs : List (ports addressWidth).outputs.Values}
    (positive : 0 < addressWidth)
    (trace : Trace (Transition addressWidth) initial inputs outputs final)
    (start : Nat)
    (within : start + BitVector.cardinality addressWidth ≤ inputs.length)
    (starts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos addressWidth)
      (fun input : (ports addressWidth).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window inputs start within))
    (offset : Fin (BitVector.cardinality addressWidth)) :
    writeObservation addressWidth
        (FramedLatency.window outputs start (by
          rw [trace.length_eq]
          exact within) offset) =
      writeControls addressWidth
        (BitVector.ofNat addressWidth offset.val) := by
  have lists := write_observations_of_marked_window positive trace start
    within starts
  have pointwise := congrArg
    (fun values : List (WriteObservation addressWidth) =>
      values[offset.val]?) lists
  have leftOccurs : offset.val <
      ((List.ofFn (FramedLatency.window outputs start (by
        rw [trace.length_eq]
        exact within))).map (writeObservation addressWidth)).length := by
    simpa only [List.length_map, List.length_ofFn] using offset.isLt
  have rightOccurs : offset.val <
      ((expectedAddresses addressWidth 0
        (BitVector.cardinality addressWidth)).map
          (writeControls addressWidth)).length := by
    simpa only [expectedAddresses, List.length_map, List.length_range']
      using offset.isLt
  have someValues := (List.getElem?_eq_getElem leftOccurs).symm.trans
    (pointwise.trans (List.getElem?_eq_getElem rightOccurs))
  have valuesEqual := Option.some.inj someValues
  simpa [expectedAddresses] using valuesEqual

theorem read_observation_at_of_marked_window
    {initial final : State addressWidth}
    {inputs : List (ports addressWidth).inputs.Values}
    {outputs : List (ports addressWidth).outputs.Values}
    (positive : 0 < addressWidth)
    (trace : Trace (Transition addressWidth) initial inputs outputs final)
    (start : Nat)
    (within : start + BitVector.cardinality addressWidth ≤ inputs.length)
    (starts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos addressWidth)
      (fun input : (ports addressWidth).inputs.Values =>
        (show Bool from input .i_readFirst) = true)
      (FramedLatency.window inputs start within))
    (offset : Fin (BitVector.cardinality addressWidth)) :
    readObservation addressWidth
        (FramedLatency.window outputs start (by
          rw [trace.length_eq]
          exact within) offset) =
      readControls addressWidth
        (BitVector.ofNat addressWidth offset.val) := by
  have lists := read_observations_of_marked_window positive trace start
    within starts
  have pointwise := congrArg
    (fun values : List (ReadObservation addressWidth) =>
      values[offset.val]?) lists
  have leftOccurs : offset.val <
      ((List.ofFn (FramedLatency.window outputs start (by
        rw [trace.length_eq]
        exact within))).map (readObservation addressWidth)).length := by
    simpa only [List.length_map, List.length_ofFn] using offset.isLt
  have rightOccurs : offset.val <
      ((expectedAddresses addressWidth 0
        (BitVector.cardinality addressWidth)).map
          (readControls addressWidth)).length := by
    simpa only [expectedAddresses, List.length_map, List.length_range']
      using offset.isLt
  have someValues := (List.getElem?_eq_getElem leftOccurs).symm.trans
    (pointwise.trans (List.getElem?_eq_getElem rightOccurs))
  have valuesEqual := Option.some.inj someValues
  simpa [expectedAddresses] using valuesEqual

/-- A complete marked write traversal establishes the exact frame schedule.
During the following traversal, later markers may restart the counter, but
the effective counter at offset `k` is still some value no greater than `k`.
This is the fact needed to rule out overwrites while the preceding frame is
being read. -/
theorem write_observations_of_marked_window_with_continuation
    {initial final : State addressWidth}
    {inputs : List (ports addressWidth).inputs.Values}
    {outputs : List (ports addressWidth).outputs.Values}
    (positive : 0 < addressWidth)
    (trace : Trace (Transition addressWidth) initial inputs outputs final)
    (start : Nat)
    (continuationLength : Nat)
    (continuationBound : continuationLength ≤
      BitVector.cardinality addressWidth)
    (within : start + BitVector.cardinality addressWidth +
        continuationLength ≤ inputs.length)
    (starts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos addressWidth)
      (fun input : (ports addressWidth).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window (length := BitVector.cardinality addressWidth)
        inputs start (by omega))) :
    (List.ofFn (FramedLatency.window
      (length := BitVector.cardinality addressWidth) outputs start (by
      rw [trace.length_eq]
      omega))).map (writeObservation addressWidth) =
        (expectedAddresses addressWidth 0
          (BitVector.cardinality addressWidth)).map
            (writeControls addressWidth) ∧
      ∀ offset : Fin continuationLength,
        ∃ value : Nat, value ≤ offset.val ∧
          writeObservation addressWidth
              (FramedLatency.window
                (length := continuationLength) outputs
                (start + BitVector.cardinality addressWidth) (by
                  rw [trace.length_eq]
                  exact within) offset) =
            writeControls addressWidth
              (BitVector.ofNat addressWidth value) := by
  have firstInputWithin : start + BitVector.cardinality addressWidth ≤
      inputs.length := by omega
  have firstOutputWithin : start + BitVector.cardinality addressWidth ≤
      outputs.length := by
    rw [trace.length_eq]
    exact firstInputWithin
  have secondInputWithin : start + BitVector.cardinality addressWidth +
      continuationLength ≤ inputs.length := within
  have secondOutputWithin : start + BitVector.cardinality addressWidth +
      continuationLength ≤ outputs.length := by
    rw [trace.length_eq]
    exact within
  obtain ⟨windowInitial, middle, windowFinal, firstTrace, secondTrace⟩ :=
    FramedLatency.exists_trace_window_pair trace start
      (BitVector.cardinality addressWidth)
      continuationLength within
  rw [← FramedLatency.ofFn_window inputs start firstInputWithin,
    ← FramedLatency.ofFn_window outputs start firstOutputWithin] at firstTrace
  rw [← FramedLatency.ofFn_window inputs
      (start + BitVector.cardinality addressWidth) secondInputWithin,
    ← FramedLatency.ofFn_window outputs
      (start + BitVector.cardinality addressWidth) secondOutputWithin]
      at secondTrace
  have markers := markerList_of_starts
    (by
      rw [BitVector.cardinality_eq_pow]
      exact Nat.two_pow_pos addressWidth)
    (fun input : (ports addressWidth).inputs.Values => input .i_first)
    inputs start firstInputWithin starts
  have projectedFirst := write_observations_of_trace firstTrace
  have runEqual := run_marked_frame addressWidth positive
    windowInitial.storedWriteAddress
  have projectedMarked :
      ((List.ofFn (FramedLatency.window outputs start firstOutputWithin)).map
          (writeObservation addressWidth), middle.storedWriteAddress) =
        ((expectedAddresses addressWidth 0
          (BitVector.cardinality addressWidth)).map
            (writeControls addressWidth), zeroAddress addressWidth) := by
    calc
      _ = let result := run windowInitial.storedWriteAddress
            ((List.ofFn (FramedLatency.window inputs start
              firstInputWithin)).map fun input =>
                (show Bool from input .i_first))
          (result.1.map (writeControls addressWidth), result.2) :=
        projectedFirst
      _ = _ := by rw [markers, runEqual]
  have firstObservations := congrArg Prod.fst projectedMarked
  have middleWrite : middle.storedWriteAddress = zeroAddress addressWidth := by
    simpa using congrArg Prod.snd projectedMarked
  have projectedSecond := write_observations_of_trace secondTrace
  rw [middleWrite] at projectedSecond
  let secondMarkers :=
    (List.ofFn (FramedLatency.window inputs
      (start + BitVector.cardinality addressWidth) secondInputWithin)).map
      fun input => (show Bool from input .i_first)
  have projectedSecondLists := congrArg Prod.fst projectedSecond
  refine ⟨firstObservations, ?_⟩
  intro offset
  have markerOccurs : offset.val < secondMarkers.length := by
    dsimp only [secondMarkers]
    simpa only [List.length_map, List.length_ofFn] using offset.isLt
  have outputOccurs : offset.val <
      ((List.ofFn (FramedLatency.window outputs
        (start + BitVector.cardinality addressWidth)
        secondOutputWithin)).map
          (writeObservation addressWidth)).length := by
    simpa only [List.length_map, List.length_ofFn] using offset.isLt
  have runOccurs : offset.val <
      ((run (zeroAddress addressWidth) secondMarkers).1.map
        (writeControls addressWidth)).length := by
    simp only [List.length_map, run_observations_length]
    exact markerOccurs
  have secondLists :
      (List.ofFn (FramedLatency.window outputs
        (start + BitVector.cardinality addressWidth)
        secondOutputWithin)).map (writeObservation addressWidth) =
      (run (zeroAddress addressWidth) secondMarkers).1.map
        (writeControls addressWidth) := by
    simpa only [Prod.fst] using projectedSecondLists
  have outputFromRun := congrArg
    (fun values : List (WriteObservation addressWidth) =>
      values[offset.val]?) secondLists
  have someValues :=
    (List.getElem?_eq_getElem outputOccurs).symm.trans
      (outputFromRun.trans (List.getElem?_eq_getElem runOccurs))
  have valuesEqual := Option.some.inj someValues
  simp only [List.getElem_map, List.getElem_ofFn] at valuesEqual
  obtain ⟨value, bound, addressEqual⟩ := run_short_observation
    addressWidth positive secondMarkers offset.val markerOccurs
      (by omega)
  refine ⟨value, bound, ?_⟩
  rw [valuesEqual]
  simpa using congrArg (writeControls addressWidth) addressEqual

end HTFFT.Silean.FinalReorder.Control
