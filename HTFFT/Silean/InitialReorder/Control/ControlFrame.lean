import HTFFT.Silean.InitialReorder.Control.Control
import Silean.Semantics.FramedLatency

/-! Complete-traversal consequences of the natural initial-reorder control
machine. -/

namespace HTFFT.Silean.InitialReorder.Control

open _root_.Silean

abbrev Observation (addressWidth : Nat) := Address addressWidth × Bool

def observe (addressWidth : Nat) (first : Bool) (state : State addressWidth) :
    Observation addressWidth :=
  (effectiveAddress addressWidth first state, state.reversed)

def run : State addressWidth → List Bool →
    List (Observation addressWidth) × State addressWidth
  | state, [] => ([], state)
  | state, first :: rest =>
      let tail := run (nextState addressWidth first state) rest
      (observe addressWidth first state :: tail.1, tail.2)

@[simp] theorem run_append (addressWidth : Nat)
    (state : State addressWidth) (left right : List Bool) :
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
    (state : State addressWidth) (markers : List Bool) :
    (run state markers).1.length = markers.length := by
  induction markers generalizing state with
  | nil => rfl
  | cons first markers induction => simp [run, induction]

def addressState (addressWidth value : Nat) (reversed : Bool) :
    State addressWidth :=
  { storedAddress := BitVector.ofNat addressWidth value
    reversed := reversed }

theorem atLast_ofNat_false (addressWidth value : Nat)
    (nextInRange : value + 1 < BitVector.cardinality addressWidth) :
    atLastAddress addressWidth (BitVector.ofNat addressWidth value) = false := by
  cases equal : atLastAddress addressWidth (BitVector.ofNat addressWidth value)
  · rfl
  · exfalso
    have vectorEqual := (atLastAddress_eq_true_iff addressWidth _).mp equal
    have numeric := congrArg (BitVector.toNat addressWidth) vectorEqual
    rw [BitVector.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      toNat_lastAddress] at numeric
    omega

theorem atLast_ofNat_last (addressWidth : Nat) :
    atLastAddress addressWidth
        (BitVector.ofNat addressWidth
          (BitVector.cardinality addressWidth - 1)) = true := by
  rw [atLastAddress_eq_true_iff]
  apply BitVector.toNat_injective addressWidth
  rw [BitVector.toNat_ofNat, toNat_lastAddress]
  have positive : 0 < BitVector.cardinality addressWidth := by
    rw [BitVector.cardinality_eq_pow]
    exact Nat.two_pow_pos addressWidth
  rw [Nat.mod_eq_of_lt (by omega)]

theorem nextState_false_beforeLast (addressWidth value : Nat)
    (reversed : Bool)
    (nextInRange : value + 1 < BitVector.cardinality addressWidth) :
    nextState addressWidth false (addressState addressWidth value reversed) =
      addressState addressWidth (value + 1) reversed := by
  apply State.ext <;>
    simp [nextState, effectiveAddress, addressState,
      increment_ofNat addressWidth value nextInRange,
      atLast_ofNat_false addressWidth value nextInRange]

theorem nextState_false_last (addressWidth : Nat) (reversed : Bool) :
    nextState addressWidth false
        (addressState addressWidth
          (BitVector.cardinality addressWidth - 1) reversed) =
      addressState addressWidth 0 (!reversed) := by
  apply State.ext
  · change _root_.Silean.Modules.Increment.incrementValue addressWidth
        (BitVector.ofNat addressWidth
          (BitVector.cardinality addressWidth - 1)) =
      BitVector.ofNat addressWidth 0
    rw [ofNat_cardinality_sub_one, increment_lastAddress]
    rfl
  · change (bif atLastAddress addressWidth
        (BitVector.ofNat addressWidth
          (BitVector.cardinality addressWidth - 1)) then
          !reversed else reversed) = !reversed
    rw [ofNat_cardinality_sub_one]
    have lastTrue : atLastAddress addressWidth
        (lastAddress addressWidth) = true :=
      (atLastAddress_eq_true_iff addressWidth _).2 rfl
    rw [lastTrue]
    exact Bool.cond_pos rfl

theorem nextState_true (addressWidth : Nat) (positive : 0 < addressWidth)
    (state : State addressWidth) :
    nextState addressWidth true state =
      addressState addressWidth 1 state.reversed := by
  have cardTwo : 2 ≤ BitVector.cardinality addressWidth := by
    rw [BitVector.cardinality_eq_pow]
    exact Nat.one_lt_two_pow (Nat.ne_of_gt positive)
  have zeroNotLast : atLastAddress addressWidth (zeroAddress addressWidth) =
      false := by
    unfold zeroAddress
    exact atLast_ofNat_false addressWidth 0 (by omega)
  apply State.ext <;>
    simp [nextState, effectiveAddress, addressState, zeroNotLast,
      oneAddress]

/-- Fewer than one complete traversal's worth of arbitrary markers cannot
toggle orientation. Resets can only reduce the numerical address relative to
ordinary counting. -/
theorem run_short_final (addressWidth start : Nat) (reversed : Bool)
    (positive : 0 < addressWidth) (markers : List Bool)
    (short : start + markers.length < BitVector.cardinality addressWidth) :
    ∃ finalAddress : Nat,
      finalAddress ≤ start + markers.length ∧
      (run (addressWidth := addressWidth)
        (addressState addressWidth start reversed) markers).2 =
          addressState addressWidth finalAddress reversed := by
  induction markers generalizing start with
  | nil => exact ⟨start, by simp, rfl⟩
  | cons first markers induction =>
      simp only [List.length_cons] at short
      cases first with
      | false =>
          have nextInRange : start + 1 <
              BitVector.cardinality addressWidth := by omega
          have tailShort : (start + 1) + markers.length <
              BitVector.cardinality addressWidth := by omega
          rw [run, nextState_false_beforeLast addressWidth start reversed
            nextInRange]
          obtain ⟨finalAddress, bound, final⟩ :=
            induction (start + 1) tailShort
          exact ⟨finalAddress, by simp only [List.length_cons]; omega, final⟩
      | true =>
          rw [run, nextState_true addressWidth positive]
          have cardTwo : 2 ≤ BitVector.cardinality addressWidth := by
            rw [BitVector.cardinality_eq_pow]
            exact Nat.one_lt_two_pow (Nat.ne_of_gt positive)
          have tailShort : 1 + markers.length <
              BitVector.cardinality addressWidth := by omega
          obtain ⟨finalAddress, bound, final⟩ :=
            induction 1 tailShort
          exact ⟨finalAddress, by simp only [List.length_cons]; omega, final⟩

/-- Observation `position` in a pure controller run is computed from the
state reached after the preceding prefix. -/
theorem run_get_eq_observe_after (addressWidth : Nat)
    (state : State addressWidth) (markers : List Bool)
    (position : Nat) (occurs : position < markers.length) :
    (run state markers).1.get ⟨position, by
      simpa [run_observations_length addressWidth state markers] using occurs⟩ =
      observe addressWidth (markers.get ⟨position, occurs⟩)
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
            (nextState addressWidth first state) markers tailOccurs

/-- During a short arbitrary continuation from address zero, orientation is
constant and the effective address at offset `position` is at most that
offset. -/
theorem run_short_observation (addressWidth : Nat) (reversed : Bool)
    (positive : 0 < addressWidth) (markers : List Bool)
    (position : Nat) (occurs : position < markers.length)
    (short : position < BitVector.cardinality addressWidth) :
    let observation := (run (addressWidth := addressWidth)
      (addressState addressWidth 0 reversed) markers).1.get
        ⟨position, by
          rw [run_observations_length]
          exact occurs⟩
    observation.2 = reversed ∧
      BitVector.toNat addressWidth observation.1 ≤ position := by
  dsimp only
  rw [run_get_eq_observe_after addressWidth
    (addressState addressWidth 0 reversed) markers position occurs]
  have prefixLength : (markers.take position).length = position := by
    simp
    omega
  obtain ⟨currentAddress, bound, current⟩ := run_short_final
    addressWidth 0 reversed positive (markers.take position) (by
      rw [prefixLength]
      simpa using short)
  have currentBound : currentAddress ≤ position := by
    rw [prefixLength] at bound
    simpa using bound
  have currentInRange : currentAddress <
      BitVector.cardinality addressWidth := by omega
  rw [current]
  unfold observe effectiveAddress addressState
  constructor
  · rfl
  · cases selected : markers.get ⟨position, occurs⟩
    · simp only [Bool.cond_false, BitVector.toNat_ofNat,
        Nat.mod_eq_of_lt currentInRange]
      exact currentBound
    · simp [zeroAddress]

def expectedObservations (addressWidth start count : Nat) (reversed : Bool) :
    List (Observation addressWidth) :=
  (List.range' start count).map fun value =>
    (BitVector.ofNat addressWidth value, reversed)

theorem run_false_traversal (addressWidth start count : Nat)
    (reversed : Bool)
    (startPositive : 0 < start)
    (startInRange : start < BitVector.cardinality addressWidth)
    (completes : start + count = BitVector.cardinality addressWidth) :
    run (addressWidth := addressWidth) (addressState addressWidth start reversed)
        (List.replicate count false) =
      (expectedObservations addressWidth start count reversed,
        addressState addressWidth 0 (!reversed)) := by
  induction count generalizing start with
  | zero => omega
  | succ count induction =>
      by_cases tailEmpty : count = 0
      · subst count
        have startLast : start = BitVector.cardinality addressWidth - 1 := by
          omega
        subst start
        simp only [List.replicate_succ, List.replicate_zero, run,
          expectedObservations, Prod.mk.injEq]
        constructor
        · simp [observe, addressState, effectiveAddress]
        · exact nextState_false_last addressWidth reversed
      · have nextInRange : start + 1 <
            BitVector.cardinality addressWidth := by
          omega
        have tailCompletes : start + 1 + count =
            BitVector.cardinality addressWidth := by omega
        have tail := induction (start + 1) (by omega) nextInRange tailCompletes
        simp only [List.replicate_succ, run]
        rw [nextState_false_beforeLast addressWidth start reversed nextInRange,
          tail]
        rfl

theorem cardinality_two_le (addressWidth : Nat) (positive : 0 < addressWidth) :
    2 ≤ BitVector.cardinality addressWidth := by
  rw [BitVector.cardinality_eq_pow]
  exact Nat.one_lt_two_pow (Nat.ne_of_gt positive)

theorem run_marked_frame (addressWidth : Nat) (positive : 0 < addressWidth)
    (initial : State addressWidth) :
    run (addressWidth := addressWidth) initial
        (true :: List.replicate
          (BitVector.cardinality addressWidth - 1) false) =
      (expectedObservations addressWidth 0
          (BitVector.cardinality addressWidth) initial.reversed,
        addressState addressWidth 0 (!initial.reversed)) := by
  have cardTwo := cardinality_two_le addressWidth positive
  have zeroNotLast : atLastAddress addressWidth (zeroAddress addressWidth) = false := by
    unfold zeroAddress
    exact atLast_ofNat_false addressWidth 0 (by omega)
  have firstNext : nextState addressWidth true initial =
      addressState addressWidth 1 initial.reversed := by
    apply State.ext <;>
      simp [nextState, effectiveAddress, addressState, zeroNotLast,
        oneAddress]
  have tail := run_false_traversal addressWidth 1
    (BitVector.cardinality addressWidth - 1) initial.reversed
    (by omega) (by omega) (by omega)
  simp only [run, firstNext]
  rw [tail]
  apply Prod.ext
  · change _ = _
    unfold expectedObservations
    rw [show BitVector.cardinality addressWidth =
      (BitVector.cardinality addressWidth - 1) + 1 by omega]
    rw [List.range'_succ]
    simp [observe, effectiveAddress, zeroAddress]
  · rfl

/-- A natural controller trace projects to the pure marker-driven run. -/
theorem observations_of_trace
    {initial final : State addressWidth}
    {inputs : List (ports addressWidth).inputs.Values}
    {outputs : List (ports addressWidth).outputs.Values}
    (trace : Trace (Transition addressWidth) initial inputs outputs final) :
    (outputs.map fun output => (output .o_address, output .o_reversed), final) =
      run (addressWidth := addressWidth) initial
        (inputs.map fun input => input .i_first) := by
  induction trace with
  | nil state => rfl
  | cons input output step rest induction =>
      rcases step with ⟨outputEqual, nextEqual⟩
      subst nextEqual
      rcases outputEqual with ⟨addressEqual, reversedEqual⟩
      simp only [List.map_cons, run]
      rw [← induction]
      rw [addressEqual, reversedEqual]
      simp only [observe]
      rfl

/-- The marker projection of a valid frame is one `true` followed by
`false` for the rest of the frame. -/
theorem markerList_of_starts
    {inputs : List (ports addressWidth).inputs.Values}
    (start : Nat)
    (within : start + BitVector.cardinality addressWidth ≤ inputs.length)
    (starts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos addressWidth)
      (fun input : (ports addressWidth).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window inputs start within)) :
    (List.ofFn (FramedLatency.window inputs start within)).map
        (fun input => (show Bool from input .i_first)) =
      true :: List.replicate
        (BitVector.cardinality addressWidth - 1) false := by
  have cardPositive : 0 < BitVector.cardinality addressWidth := by
    rw [BitVector.cardinality_eq_pow]
    exact Nat.two_pow_pos addressWidth
  apply List.ext_getElem
  · rw [List.length_map, List.length_ofFn, List.length_cons,
      List.length_replicate]
    omega
  · intro index leftIn rightIn
    simp only [List.getElem_map, List.getElem_ofFn] at leftIn ⊢
    have indexIn : index < BitVector.cardinality addressWidth := by
      simpa using leftIn
    cases index with
    | zero =>
      change (FramedLatency.window inputs start within ⟨0, by omega⟩)
        Input.i_first = true
      exact starts.first
    | succ index =>
      have unmarked := starts.not_first
        ⟨index + 1, indexIn⟩ (Nat.succ_ne_zero index)
      have equalFalse :
          (show Bool from
            (FramedLatency.window inputs start within
              ⟨index + 1, indexIn⟩) .i_first) = false := by
        cases valueEqual :
            (show Bool from
              (FramedLatency.window inputs start within
                ⟨index + 1, indexIn⟩) .i_first)
        · rfl
        · exact False.elim (unmarked valueEqual)
      simpa only [List.getElem_cons_succ, List.getElem_replicate]
        using equalFalse

/-- Over any complete marked traversal, the public controller observations
are exactly the natural address sequence with one constant, initially unknown
orientation.  State before and after the window remains hidden. -/
theorem observations_of_marked_window
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
    ∃ reversed : Bool,
      (List.ofFn (FramedLatency.window outputs start (by
        rw [trace.length_eq]
        exact within))).map
          (fun output => (output .o_address, output .o_reversed)) =
        expectedObservations addressWidth 0
          (BitVector.cardinality addressWidth) reversed := by
  have outputWithin : start + BitVector.cardinality addressWidth ≤
      outputs.length := by
    rw [trace.length_eq]
    exact within
  obtain ⟨windowInitial, windowFinal, windowTrace⟩ :=
    FramedLatency.exists_trace_window trace start
      (BitVector.cardinality addressWidth) within
  have markerList := markerList_of_starts start within starts
  have projected := observations_of_trace windowTrace
  have projectedMarked :
      ((List.ofFn (FramedLatency.window outputs start outputWithin)).map
          fun output => (output .o_address, output .o_reversed), windowFinal) =
        (expectedObservations addressWidth 0
            (BitVector.cardinality addressWidth) windowInitial.reversed,
          addressState addressWidth 0 (!windowInitial.reversed)) := by
    calc
      _ = run windowInitial
          ((List.ofFn (FramedLatency.window inputs start within)).map
            fun input => (show Bool from input .i_first)) := projected
      _ = run windowInitial
          (true :: List.replicate
            (BitVector.cardinality addressWidth - 1) false) := by
          exact congrArg (run windowInitial) markerList
      _ = _ := run_marked_frame addressWidth positive windowInitial
  have observationLists := congrArg Prod.fst projectedMarked
  exact ⟨windowInitial.reversed, observationLists⟩

/-- A marked traversal establishes both the address/orientation schedule for
that frame and the orientation used during the following traversal.  Later
markers may restart the numerical address, but cannot toggle orientation
before a complete traversal has elapsed. -/
theorem observations_of_marked_window_with_continuation
    {initial final : State addressWidth}
    {inputs : List (ports addressWidth).inputs.Values}
    {outputs : List (ports addressWidth).outputs.Values}
    (positive : 0 < addressWidth)
    (trace : Trace (Transition addressWidth) initial inputs outputs final)
    (start : Nat)
    (within : start + BitVector.cardinality addressWidth +
        BitVector.cardinality addressWidth ≤ inputs.length)
    (starts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos addressWidth)
      (fun input : (ports addressWidth).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window (length := BitVector.cardinality addressWidth)
        inputs start (by omega))) :
    ∃ reversed : Bool,
      (List.ofFn (FramedLatency.window
        (length := BitVector.cardinality addressWidth) outputs start (by
        rw [trace.length_eq]
        omega))).map
          (fun output => (output .o_address, output .o_reversed)) =
        expectedObservations addressWidth 0
          (BitVector.cardinality addressWidth) reversed ∧
      ∀ offset : Fin (BitVector.cardinality addressWidth),
        let observation := FramedLatency.window
          (length := BitVector.cardinality addressWidth) outputs
          (start + BitVector.cardinality addressWidth) (by
            rw [trace.length_eq]
            exact within) offset
        observation .o_reversed = !reversed ∧
          BitVector.toNat addressWidth (observation .o_address) ≤ offset.val := by
  have firstInputWithin : start + BitVector.cardinality addressWidth ≤
      inputs.length := by omega
  have firstOutputWithin : start + BitVector.cardinality addressWidth ≤
      outputs.length := by
    rw [trace.length_eq]
    exact firstInputWithin
  have secondInputWithin : start + BitVector.cardinality addressWidth +
      BitVector.cardinality addressWidth ≤ inputs.length := within
  have secondOutputWithin : start + BitVector.cardinality addressWidth +
      BitVector.cardinality addressWidth ≤ outputs.length := by
    rw [trace.length_eq]
    exact within
  obtain ⟨windowInitial, middle, windowFinal, firstTrace, secondTrace⟩ :=
    FramedLatency.exists_trace_window_pair trace start
      (BitVector.cardinality addressWidth)
      (BitVector.cardinality addressWidth) within
  rw [← FramedLatency.ofFn_window inputs start firstInputWithin,
    ← FramedLatency.ofFn_window outputs start firstOutputWithin] at firstTrace
  rw [← FramedLatency.ofFn_window inputs
      (start + BitVector.cardinality addressWidth) secondInputWithin,
    ← FramedLatency.ofFn_window outputs
      (start + BitVector.cardinality addressWidth) secondOutputWithin] at secondTrace
  have markerList := markerList_of_starts start firstInputWithin starts
  have projected := observations_of_trace firstTrace
  have projectedMarked :
      ((List.ofFn (FramedLatency.window outputs start firstOutputWithin)).map
          fun output => (output .o_address, output .o_reversed), middle) =
        (expectedObservations addressWidth 0
            (BitVector.cardinality addressWidth) windowInitial.reversed,
          addressState addressWidth 0 (!windowInitial.reversed)) := by
    calc
      _ = run windowInitial
          ((List.ofFn (FramedLatency.window inputs start firstInputWithin)).map
            fun input => (show Bool from input .i_first)) := projected
      _ = run windowInitial
          (true :: List.replicate
            (BitVector.cardinality addressWidth - 1) false) := by
          exact congrArg (run windowInitial) markerList
      _ = _ := run_marked_frame addressWidth positive windowInitial
  have firstObservations :
      (List.ofFn (FramedLatency.window outputs start firstOutputWithin)).map
          (fun output => (output .o_address, output .o_reversed)) =
        expectedObservations addressWidth 0
          (BitVector.cardinality addressWidth) windowInitial.reversed := by
    simpa using congrArg Prod.fst projectedMarked
  have middleEqual : middle =
      addressState addressWidth 0 (!windowInitial.reversed) := by
    simpa using congrArg Prod.snd projectedMarked
  have projectedSecond := observations_of_trace secondTrace
  rw [middleEqual] at projectedSecond
  let secondMarkers :=
    (List.ofFn (FramedLatency.window inputs
      (start + BitVector.cardinality addressWidth) secondInputWithin)).map
      fun input => (show Bool from input .i_first)
  have projectedSecondLists := congrArg Prod.fst projectedSecond
  refine ⟨windowInitial.reversed, firstObservations, ?_⟩
  intro offset
  have occurs : offset.val < secondMarkers.length := by
    change offset.val <
      ((List.ofFn (FramedLatency.window inputs
        (start + BitVector.cardinality addressWidth)
        secondInputWithin)).map
          fun input => (show Bool from input .i_first)).length
    simpa only [List.length_map, List.length_ofFn] using offset.isLt
  have projectedSecondLists' :
      (List.ofFn (FramedLatency.window outputs
          (start + BitVector.cardinality addressWidth)
          secondOutputWithin)).map
          (fun output => (output .o_address, output .o_reversed)) =
        (run (addressState addressWidth 0 (!windowInitial.reversed))
          secondMarkers).1 := by
    simpa only [Prod.fst] using projectedSecondLists
  have outputOccurs : offset.val <
      ((List.ofFn (FramedLatency.window outputs
        (start + BitVector.cardinality addressWidth)
        secondOutputWithin)).map
          (fun output => (output .o_address, output .o_reversed))).length := by
    simpa only [List.length_map, List.length_ofFn] using offset.isLt
  have runOccurs : offset.val <
      (run (addressState addressWidth 0 (!windowInitial.reversed))
        secondMarkers).1.length := by
    rw [run_observations_length]
    exact occurs
  have outputFromRun := congrArg
    (fun values : List (Observation addressWidth) => values[offset.val]?)
    projectedSecondLists'
  have someValues :=
    (List.getElem?_eq_getElem outputOccurs).symm.trans
      (outputFromRun.trans (List.getElem?_eq_getElem runOccurs))
  have valuesEqual := Option.some.inj someValues
  simp only [List.getElem_map, List.getElem_ofFn] at valuesEqual
  have outputFromRun' :
      ((FramedLatency.window outputs
        (start + BitVector.cardinality addressWidth)
        secondOutputWithin offset) .o_address,
       (FramedLatency.window outputs
        (start + BitVector.cardinality addressWidth)
        secondOutputWithin offset) .o_reversed) =
      (run (addressState addressWidth 0 (!windowInitial.reversed))
        secondMarkers).1.get ⟨offset.val, runOccurs⟩ :=
    valuesEqual
  have controlled := run_short_observation addressWidth
    (!windowInitial.reversed) positive secondMarkers offset.val occurs
      offset.isLt
  rw [← outputFromRun'] at controlled
  exact controlled

end HTFFT.Silean.InitialReorder.Control
