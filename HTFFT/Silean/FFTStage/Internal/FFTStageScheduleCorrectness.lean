import HTFFT.Silean.FFTStage.Internal.FFTStageSchedule

/-! # Correctness of the pure streaming-stage schedule

This file connects the functional two-delay commutator to the shared abstract
delay-line trace semantics, then proves its frame-relative operand and control
schedule.  It remains independent of Silean module structure.
-/

namespace HTFFT.Silean.FFTStage.Internal

open _root_.Silean

namespace Commutator

@[simp] theorem frameCoordinate_fst_val (groups delay : Nat)
    (cycle : Fin (groups * (2 * delay))) :
    (frameCoordinate groups delay cycle).1.val = cycle.val / (2 * delay) := by
  rfl

@[simp] theorem frameCoordinate_snd_val (groups delay : Nat)
    (cycle : Fin (groups * (2 * delay))) :
    (frameCoordinate groups delay cycle).2.val = cycle.val % (2 * delay) := by
  rfl

/-- In the first local half, the first paired input cycle is the output cycle
itself and the second is `delay` cycles later. -/
theorem pairedInputCycles_of_firstHalf
    (groups delay : Nat) (positive : 0 < delay)
    (cycle : Fin (groups * (2 * delay)))
    (firstHalf : (frameCoordinate groups delay cycle).2.val < delay) :
    (pairedInputCycles groups delay positive cycle).1 = cycle ∧
      (pairedInputCycles groups delay positive cycle).2.val =
        cycle.val + delay := by
  let coordinate := frameCoordinate groups delay cycle
  have cycleValue :
      cycle.val = coordinate.2.val + (2 * delay) * coordinate.1.val := by
    exact (Nat.mod_add_div cycle.val (2 * delay)).symm
  unfold pairedInputCycles
  rw [dif_pos firstHalf]
  constructor
  · apply Fin.ext
    change coordinate.2.val + (2 * delay) * coordinate.1.val = cycle.val
    exact cycleValue.symm
  · change coordinate.2.val + delay +
        (2 * delay) * coordinate.1.val = cycle.val + delay
    omega

/-- In the second local half, the second paired input cycle is the output
cycle itself and the first is `delay` cycles earlier. -/
theorem pairedInputCycles_of_secondHalf
    (groups delay : Nat) (positive : 0 < delay)
    (cycle : Fin (groups * (2 * delay)))
    (secondHalf : ¬(frameCoordinate groups delay cycle).2.val < delay) :
    (pairedInputCycles groups delay positive cycle).2 = cycle ∧
      (pairedInputCycles groups delay positive cycle).1.val + delay =
        cycle.val := by
  let coordinate := frameCoordinate groups delay cycle
  have cycleValue :
      cycle.val = coordinate.2.val + (2 * delay) * coordinate.1.val := by
    exact (Nat.mod_add_div cycle.val (2 * delay)).symm
  have phaseGe : delay ≤ coordinate.2.val := by
    dsimp only [coordinate]
    omega
  unfold pairedInputCycles
  rw [dif_neg secondHalf]
  constructor
  · apply Fin.ext
    change coordinate.2.val + (2 * delay) * coordinate.1.val = cycle.val
    exact cycleValue.symm
  · change coordinate.2.val - delay +
        (2 * delay) * coordinate.1.val + delay = cycle.val
    have phaseLt : coordinate.2.val < 2 * delay := coordinate.2.isLt
    omega

@[simp] theorem frameExecutionInputs_length
    (groups delay : Nat)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α) :
    (frameExecutionInputs groups delay frame continuation).length =
      groups * (2 * delay) + delay := by
  simp [frameExecutionInputs]

@[simp] theorem frameExecutionInputs_get_frame
    (groups delay : Nat)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (cycle : Fin (groups * (2 * delay))) :
    (frameExecutionInputs groups delay frame continuation).get
        ⟨cycle.val, by
          rw [frameExecutionInputs_length]
          omega⟩ =
      frame cycle := by
  simp [frameExecutionInputs, List.get_eq_getElem]

@[simp] theorem frameExecutionInputs_get_continuation
    (groups delay : Nat)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (cycle : Fin delay) :
    (frameExecutionInputs groups delay frame continuation).get
        ⟨groups * (2 * delay) + cycle.val, by
          rw [frameExecutionInputs_length]
          omega⟩ =
      continuation cycle := by
  simp [frameExecutionInputs, List.get_eq_getElem]

/-- Detailed execution over concatenated inputs is the concatenation of the
two executions with the intermediate state threaded between them. -/
theorem runDetailed_append (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (left right : List (Input α)) :
    runDetailed delay positive state (left ++ right) =
      let first := runDetailed delay positive state left
      let second := runDetailed delay positive first.2 right
      (first.1 ++ second.1, second.2) := by
  induction left generalizing state with
  | nil => simp [runDetailed]
  | cons input left induction =>
      simp only [List.cons_append, runDetailed]
      rw [induction]

@[simp] theorem visibleAt_zero
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (input : Input α) (inputs : List (Input α)) :
    visibleAt delay positive state (input :: inputs) 0 (by simp) =
      signals delay positive state input := by
  rfl

@[simp] theorem visibleAt_succ
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (input : Input α) (inputs : List (Input α))
    (position : Nat) (occurs : position + 1 < (input :: inputs).length) :
    visibleAt delay positive state (input :: inputs) (position + 1) occurs =
      visibleAt delay positive (nextState delay positive state input)
        inputs position (by simpa using occurs) := by
  rfl

/-- An observation in the right side of a concatenated run is the same
observation made from the state reached after the left side. -/
theorem visibleAt_append_right
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (left right : List (Input α))
    (position : Nat) (occurs : position < right.length) :
    visibleAt delay positive state (left ++ right)
        (left.length + position) (by simp; omega) =
      visibleAt delay positive (runDetailed delay positive state left).2
        right position occurs := by
  simp [visibleAt, runDetailed_append, runDetailed_length,
    List.get_eq_getElem]

/-- Every observation in a detailed run is exactly `signals` applied to the
corresponding input and the state reached at that cycle. -/
theorem exists_state_visibleAt_eq_signals
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (position : Nat) (occurs : position < inputs.length) :
    ∃ currentState,
      visibleAt delay positive state inputs position occurs =
        signals delay positive currentState
          (inputs.get ⟨position, occurs⟩) := by
  induction position generalizing state inputs with
  | zero =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs => exact ⟨state, rfl⟩
  | succ position induction =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          have tailOccurs : position < inputs.length := by
            simpa using occurs
          obtain ⟨currentState, equal⟩ := induction
            (state := nextState delay positive state input)
            (inputs := inputs) tailOccurs
          refine ⟨currentState, ?_⟩
          rw [visibleAt_succ]
          change visibleAt delay positive
              (nextState delay positive state input) inputs position _ =
            signals delay positive currentState
              (inputs.get ⟨position, tailOccurs⟩)
          exact equal

/-- A delayed frame marker resets the output-position phase on the cycle in
which that marker is observed. -/
theorem visibleAt_outputPhase_of_delayedFirst
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (position : Nat) (occurs : position < inputs.length)
    (marked :
      (visibleAt delay positive state inputs position occurs).delayedFirst =
        true) :
    (visibleAt delay positive state inputs position occurs).outputPhase =
      phaseOfNat delay positive 0 := by
  obtain ⟨currentState, equal⟩ :=
    exists_state_visibleAt_eq_signals delay positive state inputs position occurs
  rw [equal] at marked ⊢
  change DelayLine.output delay positive currentState.markerDelay = true at marked
  simp [signals, marked]

/-- On an unmarked cycle, the output-position phase advances once from the
preceding cycle.  This is the local form of moving the control count alongside
the delayed data. -/
theorem visibleAt_outputPhase_succ_of_not_delayedFirst
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (position : Nat) (occurs : position + 1 < inputs.length)
    (unmarked :
      (visibleAt delay positive state inputs (position + 1) occurs).delayedFirst =
        false) :
    (visibleAt delay positive state inputs (position + 1) occurs).outputPhase =
      phaseOfNat delay positive
        ((visibleAt delay positive state inputs position (by omega)).outputPhase.val + 1) := by
  induction position generalizing state inputs with
  | zero =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          cases inputs with
          | nil => simp at occurs
          | cons nextInput inputs =>
              rw [visibleAt_succ] at unmarked ⊢
              simp only [visibleAt_zero] at unmarked ⊢
              change DelayLine.output delay positive
                (DelayLine.next delay input.first state.markerDelay) = false
                at unmarked
              simp [nextState, signals, unmarked, nextPhase]
  | succ position induction =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          rw [visibleAt_succ] at unmarked ⊢
          exact induction (state := nextState delay positive state input)
            (inputs := inputs) (by simpa using occurs) unmarked

/-- The visible operand muxes have their defining relationship to the current
input and delay-line outputs at every position of a run. -/
theorem visibleAt_operands
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (position : Nat) (occurs : position < inputs.length) :
    let visible := visibleAt delay positive state inputs position occurs
    let input := inputs.get ⟨position, occurs⟩
    visible.operands =
      if visible.firstHalf then
        { a := visible.secondOutput, b := visible.firstOutput }
      else
        { a := visible.firstOutput, b := input.a } := by
  obtain ⟨currentState, equal⟩ :=
    exists_state_visibleAt_eq_signals delay positive state inputs position occurs
  rw [equal]
  rfl

/-- The value shifted into the first delay path at every run position. -/
theorem visibleAt_firstInput
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (position : Nat) (occurs : position < inputs.length) :
    let visible := visibleAt delay positive state inputs position occurs
    let input := inputs.get ⟨position, occurs⟩
    visible.firstInput = if visible.firstHalf then input.a else input.b := by
  obtain ⟨currentState, equal⟩ :=
    exists_state_visibleAt_eq_signals delay positive state inputs position occurs
  rw [equal]
  rfl

/-- The value shifted into the second delay path at every run position. -/
theorem visibleAt_secondInput
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (position : Nat) (occurs : position < inputs.length) :
    let visible := visibleAt delay positive state inputs position occurs
    let input := inputs.get ⟨position, occurs⟩
    visible.secondInput =
      if visible.firstHalf then input.b else visible.secondOutput := by
  obtain ⟨currentState, equal⟩ :=
    exists_state_visibleAt_eq_signals delay positive state inputs position occurs
  rw [equal]
  rfl

/-- With no frame marker, a canonical stored phase advances once per cycle. -/
theorem visibleAt_phase_of_unmarked
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (base position : Nat)
    (phaseEqual : state.phase = phaseOfNat delay positive base)
    (unmarked : inputs.Forall (fun input => input.first = false))
    (occurs : position < inputs.length) :
    (visibleAt delay positive state inputs position occurs).phase =
      phaseOfNat delay positive (base + position) := by
  induction position generalizing state inputs base with
  | zero =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          rw [List.forall_cons] at unmarked
          have inputFalse := unmarked.1
          simp [signals, inputFalse, phaseEqual]
  | succ position induction =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          rw [List.forall_cons] at unmarked
          have inputFalse := unmarked.1
          have tailUnmarked := unmarked.2
          have tailOccurs : position < inputs.length := by
            simpa using occurs
          rw [visibleAt_succ]
          have nextPhaseEqual :
              (nextState delay positive state input).phase =
                phaseOfNat delay positive (base + 1) := by
            simp [nextState, inputFalse, phaseEqual]
          have later := induction
            (state := nextState delay positive state input)
            (inputs := inputs) (base := base + 1) nextPhaseEqual
            tailUnmarked tailOccurs
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later

/-- A marker on the first cycle makes the observed phase zero immediately;
subsequent unmarked cycles have the canonical frame-relative phase. -/
theorem visibleAt_phase_of_marked_start
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (firstInput : Input α)
    (remainingInputs : List (Input α)) (position : Nat)
    (marked : firstInput.first = true)
    (unmarked : remainingInputs.Forall (fun input => input.first = false))
    (occurs : position < (firstInput :: remainingInputs).length) :
    (visibleAt delay positive state (firstInput :: remainingInputs)
        position occurs).phase =
      phaseOfNat delay positive position := by
  cases position with
  | zero => simp [signals, marked]
  | succ position =>
      rw [visibleAt_succ]
      have nextPhaseEqual :
          (nextState delay positive state firstInput).phase =
            phaseOfNat delay positive 1 := by
        simp [nextState, marked]
      have tailOccurs : position < remainingInputs.length := by
        simpa using occurs
      have later := visibleAt_phase_of_unmarked delay positive
        (nextState delay positive state firstInput) remainingInputs
        1 position nextPhaseEqual unmarked tailOccurs
      simpa [Nat.add_comm] using later

/-- Canonical phase over an unmarked prefix; markers after `position` are
irrelevant. -/
theorem visibleAt_phase_of_unmarked_through
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (base position : Nat)
    (phaseEqual : state.phase = phaseOfNat delay positive base)
    (unmarked : ∀ (offset : Nat) (occurs : offset < inputs.length),
      offset ≤ position → (inputs.get ⟨offset, occurs⟩).first = false)
    (occurs : position < inputs.length) :
    (visibleAt delay positive state inputs position occurs).phase =
      phaseOfNat delay positive (base + position) := by
  induction position generalizing state inputs base with
  | zero =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          have inputFalse := unmarked 0 (by simp) (by omega)
          have inputFalse' : input.first = false := by simpa using inputFalse
          simp [signals, inputFalse', phaseEqual]
  | succ position induction =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          have inputFalse := unmarked 0 (by simp) (by omega)
          have inputFalse' : input.first = false := by simpa using inputFalse
          have tailOccurs : position < inputs.length := by
            simpa using occurs
          have tailUnmarked : ∀ (offset : Nat)
              (offsetOccurs : offset < inputs.length),
              offset ≤ position →
                (inputs.get ⟨offset, offsetOccurs⟩).first = false := by
            intro offset offsetOccurs within
            have originalOccurs : offset + 1 < (input :: inputs).length := by
              simp only [List.length_cons]
              omega
            have original := unmarked (offset + 1) originalOccurs (by omega)
            exact original
          rw [visibleAt_succ]
          have nextPhaseEqual :
              (nextState delay positive state input).phase =
                phaseOfNat delay positive (base + 1) := by
            simp [nextState, inputFalse', phaseEqual]
          have later := induction
            (state := nextState delay positive state input)
            (inputs := inputs) (base := base + 1) nextPhaseEqual
            tailUnmarked tailOccurs
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later

/-- A marked cycle followed by an unmarked prefix has canonical
frame-relative phase, regardless of earlier state or markers after the queried
position. -/
theorem visibleAt_phase_of_marked_through
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (position : Nat)
    (occurs : position < inputs.length)
    (marked : (inputs.get ⟨0, by omega⟩).first = true)
    (unmarked : ∀ (offset : Nat) (occurs : offset < inputs.length),
      0 < offset → offset ≤ position →
        (inputs.get ⟨offset, occurs⟩).first = false) :
    (visibleAt delay positive state inputs position occurs).phase =
      phaseOfNat delay positive position := by
  cases position with
  | zero =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          have inputMarked : input.first = true := by simpa using marked
          simp [signals, inputMarked]
  | succ position =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          have inputMarked : input.first = true := by simpa using marked
          have tailOccurs : position < inputs.length := by
            simpa using occurs
          rw [visibleAt_succ]
          have nextPhaseEqual :
              (nextState delay positive state input).phase =
                phaseOfNat delay positive 1 := by
            simp [nextState, inputMarked]
          have tailUnmarked : ∀ (offset : Nat)
              (offsetOccurs : offset < inputs.length),
              offset ≤ position →
                (inputs.get ⟨offset, offsetOccurs⟩).first = false := by
            intro offset offsetOccurs within
            have originalOccurs : offset + 1 < (input :: inputs).length := by
              simp only [List.length_cons]
              omega
            exact unmarked (offset + 1) originalOccurs (by omega) (by omega)
          have later := visibleAt_phase_of_unmarked_through delay positive
            (nextState delay positive state input) inputs 1 position
            nextPhaseEqual tailUnmarked tailOccurs
          simpa [Nat.add_comm] using later

/-- A valid marked input frame fixes the input-routing phase at every frame
cycle, independently of the phase stored before the marker. -/
theorem frame_inputPhase
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay) (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input α => input.first = true) frame)
    (cycle : Fin (groups * (2 * delay))) :
    (visibleAt delay positive state
      (frameExecutionInputs groups delay frame continuation)
      cycle.val (by
        rw [frameExecutionInputs_length]
        omega)).phase =
      phaseOfNat delay positive cycle.val := by
  let inputs := frameExecutionInputs groups delay frame continuation
  have occurs : cycle.val < inputs.length := by
    dsimp only [inputs]
    rw [frameExecutionInputs_length]
    omega
  have marked : (inputs.get ⟨0, by omega⟩).first = true := by
    have inputEqual : inputs.get ⟨0, by omega⟩ =
        frame ⟨0, by positivity⟩ := by
      dsimp only [inputs]
      convert frameExecutionInputs_get_frame groups delay frame continuation
        ⟨0, by positivity⟩ using 1
    rw [inputEqual]
    exact starts.first
  have unmarked : ∀ (offset : Nat) (offsetOccurs : offset < inputs.length),
      0 < offset → offset ≤ cycle.val →
        (inputs.get ⟨offset, offsetOccurs⟩).first = false := by
    intro offset offsetOccurs nonzero within
    have withinFrame : offset < groups * (2 * delay) := by
      exact lt_of_le_of_lt within cycle.isLt
    let frameCycle : Fin (groups * (2 * delay)) := ⟨offset, withinFrame⟩
    have inputEqual : inputs.get ⟨offset, offsetOccurs⟩ = frame frameCycle := by
      dsimp only [inputs]
      convert frameExecutionInputs_get_frame groups delay frame continuation
        frameCycle using 1
    rw [inputEqual]
    have frameCycleNonzero : frameCycle.val ≠ 0 := by
      dsimp only [frameCycle]
      omega
    have notMarked := starts.not_first frameCycle frameCycleNonzero
    cases marker : (frame frameCycle).first <;> simp_all
  exact visibleAt_phase_of_marked_through delay positive state inputs
    cycle.val occurs marked unmarked

/-- Final stored phase after an entirely unmarked run. -/
theorem runDetailed_finalPhase_of_unmarked
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α)) (base : Nat)
    (phaseEqual : state.phase = phaseOfNat delay positive base)
    (unmarked : inputs.Forall (fun input => input.first = false)) :
    (runDetailed delay positive state inputs).2.phase =
      phaseOfNat delay positive (base + inputs.length) := by
  induction inputs generalizing state base with
  | nil => simpa [runDetailed] using phaseEqual
  | cons input inputs induction =>
      rw [List.forall_cons] at unmarked
      have inputFalse := unmarked.1
      have nextPhaseEqual :
          (nextState delay positive state input).phase =
            phaseOfNat delay positive (base + 1) := by
        simp [nextState, inputFalse, phaseEqual]
      have later := induction (nextState delay positive state input)
        (base + 1) nextPhaseEqual unmarked.2
      simpa [runDetailed, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using later

/-- Final stored phase after a marked first cycle followed by an unmarked
frame prefix. -/
theorem runDetailed_finalPhase_of_marked_start
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (firstInput : Input α)
    (remainingInputs : List (Input α))
    (marked : firstInput.first = true)
    (unmarked : remainingInputs.Forall (fun input => input.first = false)) :
    (runDetailed delay positive state (firstInput :: remainingInputs)).2.phase =
      phaseOfNat delay positive (remainingInputs.length + 1) := by
  have nextPhaseEqual :
      (nextState delay positive state firstInput).phase =
        phaseOfNat delay positive 1 := by
    simp [nextState, marked]
  have later := runDetailed_finalPhase_of_unmarked delay positive
    (nextState delay positive state firstInput) remainingInputs 1
    nextPhaseEqual unmarked
  simpa [runDetailed, Nat.add_comm] using later

/-- A marker at the head of a nonempty run followed by only unmarked inputs
makes the final stored phase depend only on the run length. -/
theorem runDetailed_finalPhase_of_marked
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (nonempty : 0 < inputs.length)
    (marked : (inputs.get ⟨0, nonempty⟩).first = true)
    (unmarked : ∀ (offset : Nat) (occurs : offset < inputs.length),
      0 < offset → (inputs.get ⟨offset, occurs⟩).first = false) :
    (runDetailed delay positive state inputs).2.phase =
      phaseOfNat delay positive inputs.length := by
  cases inputs with
  | nil => simp at nonempty
  | cons first remaining =>
      have firstMarked : first.first = true := by simpa using marked
      have remainingUnmarked :
          remaining.Forall (fun input => input.first = false) := by
        rw [List.forall_iff_forall_mem, List.forall_mem_iff_get]
        intro index
        have original := unmarked (index.val + 1) (by simp) (by omega)
        exact original
      simpa using runDetailed_finalPhase_of_marked_start delay positive state
        first remaining firstMarked remainingUnmarked

/-- After consuming a valid complete frame, the input-routing phase is back
at zero because the frame comprises a whole number of local periods. -/
theorem frame_finalPhase
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay) (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input α => input.first = true) frame) :
    (runDetailed delay positive state (List.ofFn frame)).2.phase =
      phaseOfNat delay positive 0 := by
  let frameInputs := List.ofFn frame
  have frameLength : frameInputs.length = groups * (2 * delay) := by
    simp [frameInputs]
  have nonempty : 0 < frameInputs.length := by
    rw [frameLength]
    positivity
  have marked : (frameInputs.get ⟨0, nonempty⟩).first = true := by
    dsimp only [frameInputs]
    simpa using starts.first
  have unmarked : ∀ (offset : Nat) (occurs : offset < frameInputs.length),
      0 < offset → (frameInputs.get ⟨offset, occurs⟩).first = false := by
    intro offset occurs nonzero
    let cycle : Fin (groups * (2 * delay)) := ⟨offset, by omega⟩
    have notMarked := starts.not_first cycle (by
      dsimp only [cycle]
      omega)
    have inputEqual : frameInputs.get ⟨offset, occurs⟩ = frame cycle := by
      dsimp only [frameInputs]
      simp [cycle, List.get_eq_getElem]
    rw [inputEqual]
    cases marker : (frame cycle).first <;> simp_all
  have final := runDetailed_finalPhase_of_marked delay positive state frameInputs
    nonempty marked unmarked
  rw [frameLength] at final
  rw [final]
  apply Fin.ext
  simp [phaseOfNat]

/-- Markers may reset phase, so after `position` cycles the effective phase is
at most the initial bound plus `position`. -/
theorem visibleAt_phase_val_le
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (base position : Nat) (phaseBound : state.phase.val ≤ base)
    (occurs : position < inputs.length) :
    (visibleAt delay positive state inputs position occurs).phase.val ≤
      base + position := by
  induction position generalizing state inputs base with
  | zero =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          rw [visibleAt_zero]
          simp only [signals]
          exact (effectivePhase_val_le delay positive state.phase input.first).trans
            (by simpa using phaseBound)
  | succ position induction =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          have tailOccurs : position < inputs.length := by
            simpa using occurs
          rw [visibleAt_succ]
          have nextBound :
              (nextState delay positive state input).phase.val ≤ base + 1 := by
            simp only [nextState]
            exact (nextPhase_val_le_succ delay positive state.phase input.first).trans
              (by omega)
          have later := induction
            (state := nextState delay positive state input)
            (inputs := inputs) (base := base + 1) nextBound tailOccurs
          omega

/-- The stored `firstHalf` selector always describes the visible effective
phase. -/
theorem visibleAt_firstHalf_eq
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (position : Nat) (occurs : position < inputs.length) :
    (visibleAt delay positive state inputs position occurs).firstHalf =
      inFirstHalf delay
        (visibleAt delay positive state inputs position occurs).phase := by
  induction position generalizing state inputs with
  | zero =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs => simp [signals]
  | succ position induction =>
      cases inputs with
      | nil => simp at occurs
      | cons input inputs =>
          rw [visibleAt_succ]
          exact induction (state := nextState delay positive state input)
            (inputs := inputs) (by simpa using occurs)

/-- The input mux selector follows the local phase of every valid marked
frame. -/
theorem frame_inputFirstHalf
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay) (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input α => input.first = true) frame)
    (cycle : Fin (groups * (2 * delay))) :
    (visibleAt delay positive state
      (frameExecutionInputs groups delay frame continuation)
      cycle.val (by
        rw [frameExecutionInputs_length]
        omega)).firstHalf =
      decide ((frameCoordinate groups delay cycle).2.val < delay) := by
  rw [visibleAt_firstHalf_eq]
  rw [frame_inputPhase groups delay groupsPositive positive state frame
    continuation starts cycle]
  rfl

/-- During the first `delay` cycles after a canonical phase-zero state, the
commutator remains in its first half even if additional markers arrive. -/
theorem visibleAt_firstHalf_of_phase_zero
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (position : Nat) (phaseZero : state.phase = phaseOfNat delay positive 0)
    (withinHalf : position < delay)
    (occurs : position < inputs.length) :
    (visibleAt delay positive state inputs position occurs).firstHalf = true := by
  have initialZero : state.phase.val ≤ 0 := by
    rw [phaseZero]
    simp [phaseOfNat]
  have phaseLt :
      (visibleAt delay positive state inputs position occurs).phase.val < delay := by
    have := visibleAt_phase_val_le delay positive state inputs 0 position
      initialZero occurs
    omega
  rw [visibleAt_firstHalf_eq]
  simp [inFirstHalf, phaseLt]

/-- At the operand-output boundary the commutator selector is the opposite
half of the frame-relative output phase.  The final half-period remains true
even while arbitrary continuation traffic enters. -/
theorem frame_outputFirstHalf
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay) (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input α => input.first = true) frame)
    (cycle : Fin (groups * (2 * delay))) :
    (frameSignal groups delay positive state frame continuation cycle).firstHalf =
      decide (delay ≤ (frameCoordinate groups delay cycle).2.val) := by
  let coordinate := frameCoordinate groups delay cycle
  by_cases firstHalf : coordinate.2.val < delay
  · have expectedFalse : decide (delay ≤ coordinate.2.val) = false := by
      simp [show ¬delay ≤ coordinate.2.val by omega]
    rw [expectedFalse]
    have paired := pairedInputCycles_of_firstHalf groups delay positive cycle
      firstHalf
    let physicalCycle := (pairedInputCycles groups delay positive cycle).2
    have physicalValue : physicalCycle.val = cycle.val + delay := paired.2
    have phaseValue :
        (frameCoordinate groups delay physicalCycle).2.val =
          coordinate.2.val + delay := by
      change physicalCycle.val % (2 * delay) = coordinate.2.val + delay
      rw [physicalValue, Nat.add_mod]
      rw [Nat.mod_eq_of_lt (show delay < 2 * delay by omega)]
      change (coordinate.2.val + delay) % (2 * delay) =
        coordinate.2.val + delay
      rw [Nat.mod_eq_of_lt]
      omega
    have selector := frame_inputFirstHalf groups delay groupsPositive positive
      state frame continuation starts physicalCycle
    rw [phaseValue] at selector
    have notFirst : ¬ coordinate.2.val + delay < delay := by omega
    simp [notFirst] at selector
    simpa [frameSignal, physicalValue, Nat.add_comm] using selector
  · have secondHalf : delay ≤ coordinate.2.val := by omega
    have expected : decide (delay ≤ coordinate.2.val) = true := by
      simp [secondHalf]
    rw [expected]
    by_cases withinFrame : delay + cycle.val < groups * (2 * delay)
    · let physicalCycle : Fin (groups * (2 * delay)) :=
        ⟨delay + cycle.val, withinFrame⟩
      have phaseValue :
          (frameCoordinate groups delay physicalCycle).2.val =
            coordinate.2.val - delay := by
        change (delay + cycle.val) % (2 * delay) =
          coordinate.2.val - delay
        rw [Nat.add_comm, Nat.add_mod]
        rw [Nat.mod_eq_of_lt (show delay < 2 * delay by omega)]
        change (coordinate.2.val + delay) % (2 * delay) =
          coordinate.2.val - delay
        have sumEqual : coordinate.2.val + delay =
            coordinate.2.val - delay + 2 * delay := by omega
        rw [sumEqual, Nat.add_mod]
        simp only [Nat.mod_self, Nat.add_zero, Nat.mod_mod]
        have phaseLt := coordinate.2.isLt
        exact Nat.mod_eq_of_lt (by omega)
      have selector := frame_inputFirstHalf groups delay groupsPositive positive
        state frame continuation starts physicalCycle
      rw [phaseValue] at selector
      have inFirst : coordinate.2.val - delay < delay := by
        have phaseLt := coordinate.2.isLt
        omega
      simp [inFirst] at selector
      simpa [frameSignal, physicalCycle] using selector
    · let frameInputs := List.ofFn frame
      let continuationInputs := List.ofFn continuation
      let tailOffset := delay + cycle.val - groups * (2 * delay)
      have tailOffsetLt : tailOffset < delay := by
        dsimp only [tailOffset]
        have cycleLt := cycle.isLt
        omega
      have tailOccurs : tailOffset < continuationInputs.length := by
        simpa [continuationInputs] using tailOffsetLt
      have phaseZero :
          (runDetailed delay positive state frameInputs).2.phase =
            phaseOfNat delay positive 0 := by
        dsimp only [frameInputs]
        exact frame_finalPhase groups delay groupsPositive positive state frame
          starts
      have tailSelector := visibleAt_firstHalf_of_phase_zero delay positive
        (runDetailed delay positive state frameInputs).2 continuationInputs
        tailOffset phaseZero tailOffsetLt tailOccurs
      have shifted := visibleAt_append_right delay positive state frameInputs
        continuationInputs tailOffset tailOccurs
      have shiftedSelector := congrArg Signals.firstHalf shifted
      change (visibleAt delay positive state
        (frameInputs ++ continuationInputs) (delay + cycle.val) _).firstHalf = true
      have positionEqual : frameInputs.length + tailOffset =
          delay + cycle.val := by
        simp [frameInputs, tailOffset]
        omega
      simpa only [positionEqual] using shiftedSelector.trans tailSelector

/-- The first storage path of a detailed commutator run is an ordinary
`delay`-cycle delay-line trace. -/
theorem runDetailed_markerDelay_trace
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α)) :
    let result := runDetailed delay positive state inputs
    Trace (_root_.Silean.DelayLine.Step delay) state.markerDelay
      (inputs.map Input.first)
      (result.1.map Signals.delayedFirst) result.2.markerDelay := by
  induction inputs generalizing state with
  | nil => exact .nil state.markerDelay
  | cons input inputs induction =>
      simp only [runDetailed, List.map_cons]
      apply Trace.cons
      · exact DelayLine.step delay positive input.first state.markerDelay
      · exact induction (nextState delay positive state input)

/-- `i_first` observed at cycle `t` reaches the output-position controller at
cycle `t + delay`, independently of its initial delay contents. -/
theorem marker_reaches_output
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (t : Nat) (inputOccurs : t < inputs.length)
    (outputOccurs : t + delay < inputs.length) :
    (visibleAt delay positive state inputs (t + delay) outputOccurs).delayedFirst =
      (inputs.get ⟨t, inputOccurs⟩).first := by
  let result := runDetailed delay positive state inputs
  have trace := runDetailed_markerDelay_trace delay positive state inputs
  have delayed := _root_.Silean.DelayLine.input_reaches_output trace t
    (by simpa [result] using inputOccurs)
    (by simpa [result, runDetailed_length] using outputOccurs)
  simpa only [visibleAt, List.get_eq_getElem, List.getElem_map] using delayed

/-- The marker observed with one frame-relative operand pair is the marker
that entered with the corresponding frame cycle. -/
theorem frame_delayedFirst
    (groups delay : Nat) (positive : 0 < delay)
    (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (cycle : Fin (groups * (2 * delay))) :
    (frameSignal groups delay positive state frame continuation cycle).delayedFirst =
      (frame cycle).first := by
  let inputs := frameExecutionInputs groups delay frame continuation
  have inputOccurs : cycle.val < inputs.length := by
    dsimp only [inputs]
    rw [frameExecutionInputs_length]
    omega
  have outputOccurs : cycle.val + delay < inputs.length := by
    dsimp only [inputs]
    rw [frameExecutionInputs_length]
    omega
  have delayed := marker_reaches_output delay positive state inputs cycle.val
    inputOccurs outputOccurs
  have inputEqual : inputs.get ⟨cycle.val, inputOccurs⟩ = frame cycle := by
    dsimp only [inputs]
    convert frameExecutionInputs_get_frame groups delay frame continuation cycle
      using 1
  rw [inputEqual] at delayed
  simpa [frameSignal, inputs, Nat.add_comm] using delayed

/-- The output-position count attached to every operand pair is the canonical
frame-relative local phase.  A delayed copy of `i_first` establishes phase
zero, after which the count advances once per result. -/
theorem frame_outputPhase
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay) (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input α => input.first = true) frame)
    (cycle : Fin (groups * (2 * delay))) :
    (frameSignal groups delay positive state frame continuation cycle).outputPhase =
      scheduledPhase groups delay cycle := by
  let inputs := frameExecutionInputs groups delay frame continuation
  have exactPhase : ∀ (position : Nat),
      (positionLt : position < groups * (2 * delay)) →
      (visibleAt delay positive state inputs (delay + position) (by
        dsimp only [inputs]
        rw [frameExecutionInputs_length]
        omega)).outputPhase =
        phaseOfNat delay positive position := by
    intro position positionLt
    induction position with
    | zero =>
        let firstCycle : Fin (groups * (2 * delay)) :=
          ⟨0, by positivity⟩
        have delayedMarker := frame_delayedFirst groups delay positive state
          frame continuation firstCycle
        have marked :
            (visibleAt delay positive state inputs (delay + 0) (by
              dsimp only [inputs]
              rw [frameExecutionInputs_length]
              omega)).delayedFirst = true := by
          change (frameSignal groups delay positive state frame continuation
            firstCycle).delayedFirst = true
          rw [delayedMarker]
          exact starts.first
        exact visibleAt_outputPhase_of_delayedFirst delay positive state inputs
          (delay + 0) (by
            dsimp only [inputs]
            rw [frameExecutionInputs_length]
            omega) marked
    | succ position induction =>
        have previousLt : position < groups * (2 * delay) := by omega
        let currentCycle : Fin (groups * (2 * delay)) :=
          ⟨position + 1, positionLt⟩
        have delayedMarker := frame_delayedFirst groups delay positive state
          frame continuation currentCycle
        have unmarked :
            (visibleAt delay positive state inputs
              ((delay + position) + 1) (by
                dsimp only [inputs]
                rw [frameExecutionInputs_length]
                omega)).delayedFirst = false := by
          have notMarked := starts.not_first currentCycle (by
            dsimp only [currentCycle]
            omega)
          have currentFalse : (frame currentCycle).first = false := by
            cases marker : (frame currentCycle).first <;> simp_all
          change (frameSignal groups delay positive state frame continuation
            currentCycle).delayedFirst = false
          rw [delayedMarker]
          exact currentFalse
        have advanced :=
          visibleAt_outputPhase_succ_of_not_delayedFirst delay positive state
            inputs (delay + position) (by
              dsimp only [inputs]
              rw [frameExecutionInputs_length]
              omega) unmarked
        rw [induction previousLt] at advanced
        simpa [Nat.add_assoc] using advanced
  have phaseEqual := exactPhase cycle.val cycle.isLt
  change (visibleAt delay positive state inputs (delay + cycle.val) _).outputPhase =
    scheduledPhase groups delay cycle
  rw [phaseEqual]
  apply Fin.ext
  rfl

/-- The first storage path of a detailed commutator run is an ordinary
`delay`-cycle delay-line trace. -/
theorem runDetailed_firstDelay_trace
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α)) :
    let result := runDetailed delay positive state inputs
    Trace (_root_.Silean.DelayLine.Step delay) state.firstDelay
      (result.1.map Signals.firstInput)
      (result.1.map Signals.firstOutput) result.2.firstDelay := by
  induction inputs generalizing state with
  | nil => exact .nil state.firstDelay
  | cons input inputs induction =>
      simp only [runDetailed, List.map_cons]
      apply Trace.cons
      · exact DelayLine.step delay positive
          (signals delay positive state input).firstInput state.firstDelay
      · exact induction (nextState delay positive state input)

/-- The second storage path of a detailed commutator run is an ordinary
`delay`-cycle delay-line trace. -/
theorem runDetailed_secondDelay_trace
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α)) :
    let result := runDetailed delay positive state inputs
    Trace (_root_.Silean.DelayLine.Step delay) state.secondDelay
      (result.1.map Signals.secondInput)
      (result.1.map Signals.secondOutput) result.2.secondDelay := by
  induction inputs generalizing state with
  | nil => exact .nil state.secondDelay
  | cons input inputs induction =>
      simp only [runDetailed, List.map_cons]
      apply Trace.cons
      · exact DelayLine.step delay positive
          (signals delay positive state input).secondInput state.secondDelay
      · exact induction (nextState delay positive state input)

/-- A value selected for the first delay path at cycle `t` is the first-path
output at cycle `t + delay`, independently of the initial delay contents. -/
theorem firstInput_reaches_output
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (t : Nat) (inputOccurs : t < inputs.length)
    (outputOccurs : t + delay < inputs.length) :
    let visible := (runDetailed delay positive state inputs).1
    (visible.get ⟨t + delay, by
      have lengthEqual := runDetailed_length delay positive state inputs
      dsimp only [visible]
      omega⟩).firstOutput =
      (visible.get ⟨t, by
        have lengthEqual := runDetailed_length delay positive state inputs
        dsimp only [visible]
        omega⟩).firstInput := by
  let result := runDetailed delay positive state inputs
  have trace := runDetailed_firstDelay_trace delay positive state inputs
  have delayed := _root_.Silean.DelayLine.input_reaches_output trace t
    (by simpa [result, runDetailed_length] using inputOccurs)
    (by simpa [result, runDetailed_length] using outputOccurs)
  simpa only [List.get_eq_getElem, List.getElem_map] using delayed

/-- A value selected for the second delay path at cycle `t` is the second-path
output at cycle `t + delay`, independently of the initial delay contents. -/
theorem secondInput_reaches_output
    (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (t : Nat) (inputOccurs : t < inputs.length)
    (outputOccurs : t + delay < inputs.length) :
    let visible := (runDetailed delay positive state inputs).1
    (visible.get ⟨t + delay, by
      have lengthEqual := runDetailed_length delay positive state inputs
      dsimp only [visible]
      omega⟩).secondOutput =
      (visible.get ⟨t, by
        have lengthEqual := runDetailed_length delay positive state inputs
        dsimp only [visible]
        omega⟩).secondInput := by
  let result := runDetailed delay positive state inputs
  have trace := runDetailed_secondDelay_trace delay positive state inputs
  have delayed := _root_.Silean.DelayLine.input_reaches_output trace t
    (by simpa [result, runDetailed_length] using inputOccurs)
    (by simpa [result, runDetailed_length] using outputOccurs)
  simpa only [List.get_eq_getElem, List.getElem_map] using delayed

/-- Frame-level form of the first delay path: the value selected at input
cycle `t` is visible from that path with operand pair `t`. -/
theorem frame_firstOutput
    (groups delay : Nat) (positive : 0 < delay)
    (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (cycle : Fin (groups * (2 * delay))) :
    (frameSignal groups delay positive state frame continuation cycle).firstOutput =
      (visibleAt delay positive state
        (frameExecutionInputs groups delay frame continuation)
        cycle.val (by
          rw [frameExecutionInputs_length]
          omega)).firstInput := by
  let inputs := frameExecutionInputs groups delay frame continuation
  have inputOccurs : cycle.val < inputs.length := by
    dsimp only [inputs]
    rw [frameExecutionInputs_length]
    omega
  have outputOccurs : cycle.val + delay < inputs.length := by
    dsimp only [inputs]
    rw [frameExecutionInputs_length]
    omega
  have delayed := firstInput_reaches_output delay positive state inputs
    cycle.val inputOccurs outputOccurs
  simpa [frameSignal, visibleAt, inputs, Nat.add_comm] using delayed

/-- Frame-level form of the second delay path. -/
theorem frame_secondOutput
    (groups delay : Nat) (positive : 0 < delay)
    (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (cycle : Fin (groups * (2 * delay))) :
    (frameSignal groups delay positive state frame continuation cycle).secondOutput =
      (visibleAt delay positive state
        (frameExecutionInputs groups delay frame continuation)
        cycle.val (by
          rw [frameExecutionInputs_length]
          omega)).secondInput := by
  let inputs := frameExecutionInputs groups delay frame continuation
  have inputOccurs : cycle.val < inputs.length := by
    dsimp only [inputs]
    rw [frameExecutionInputs_length]
    omega
  have outputOccurs : cycle.val + delay < inputs.length := by
    dsimp only [inputs]
    rw [frameExecutionInputs_length]
    omega
  have delayed := secondInput_reaches_output delay positive state inputs
    cycle.val inputOccurs outputOccurs
  simpa [frameSignal, visibleAt, inputs, Nat.add_comm] using delayed

/-- Value selected into the first storage path at a frame input cycle. -/
theorem frame_firstInput
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay) (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input α => input.first = true) frame)
    (cycle : Fin (groups * (2 * delay))) :
    let visible := visibleAt delay positive state
      (frameExecutionInputs groups delay frame continuation)
      cycle.val (by
        rw [frameExecutionInputs_length]
        omega)
    visible.firstInput =
      if (frameCoordinate groups delay cycle).2.val < delay then
        (frame cycle).a
      else
        (frame cycle).b := by
  have selected := visibleAt_firstInput delay positive state
    (frameExecutionInputs groups delay frame continuation) cycle.val (by
      rw [frameExecutionInputs_length]
      omega)
  have selector := frame_inputFirstHalf groups delay groupsPositive positive
    state frame continuation starts cycle
  have inputEqual := frameExecutionInputs_get_frame groups delay frame
    continuation cycle
  dsimp only at selected ⊢
  rw [selector, inputEqual] at selected
  simpa using selected

/-- Value selected into the second storage path at a frame input cycle. -/
theorem frame_secondInput
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay) (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input α => input.first = true) frame)
    (cycle : Fin (groups * (2 * delay))) :
    let visible := visibleAt delay positive state
      (frameExecutionInputs groups delay frame continuation)
      cycle.val (by
        rw [frameExecutionInputs_length]
        omega)
    visible.secondInput =
      if (frameCoordinate groups delay cycle).2.val < delay then
        (frame cycle).b
      else
        visible.secondOutput := by
  have selected := visibleAt_secondInput delay positive state
    (frameExecutionInputs groups delay frame continuation) cycle.val (by
      rw [frameExecutionInputs_length]
      omega)
  have selector := frame_inputFirstHalf groups delay groupsPositive positive
    state frame continuation starts cycle
  have inputEqual := frameExecutionInputs_get_frame groups delay frame
    continuation cycle
  dsimp only at selected ⊢
  rw [selector, inputEqual] at selected
  simpa using selected

/-- Frame-level statement of the final operand mux. -/
theorem frame_operands_mux
    (groups delay : Nat) (positive : 0 < delay)
    (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (cycle : Fin (groups * (2 * delay))) :
    let inputs := frameExecutionInputs groups delay frame continuation
    let visible := frameSignal groups delay positive state frame continuation cycle
    visible.operands =
      if visible.firstHalf then
        { a := visible.secondOutput, b := visible.firstOutput }
      else
        { a := visible.firstOutput
          b := (inputs.get ⟨delay + cycle.val, by
            rw [frameExecutionInputs_length]
            omega⟩).a } := by
  simpa [frameSignal] using visibleAt_operands delay positive state
    (frameExecutionInputs groups delay frame continuation)
    (delay + cycle.val) (by
      rw [frameExecutionInputs_length]
      omega)

/-- The two-delay commutator presents exactly the statelessly scheduled
operand pair for every output coordinate of a valid frame.  In particular,
the result is independent of the phase and delay contents preceding
`i_first`. -/
theorem frame_operands
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay) (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input α => input.first = true) frame)
    (cycle : Fin (groups * (2 * delay))) :
    (frameSignal groups delay positive state frame continuation cycle).operands =
      scheduledOperands groups delay positive frame cycle := by
  let inputs := frameExecutionInputs groups delay frame continuation
  let coordinate := frameCoordinate groups delay cycle
  let pair := pairedInputCycles groups delay positive cycle
  have mux := frame_operands_mux groups delay positive state frame continuation
    cycle
  dsimp only at mux
  have outputSelector := frame_outputFirstHalf groups delay groupsPositive
    positive state frame continuation starts cycle
  by_cases firstHalf : coordinate.2.val < delay
  · have firstHalfCycle :
        (frameCoordinate groups delay cycle).2.val < delay := by
      simpa [coordinate] using firstHalf
    have notSecondCycle :
        ¬delay ≤ (frameCoordinate groups delay cycle).2.val := by omega
    have outputFalse :
        (frameSignal groups delay positive state frame continuation cycle).firstHalf =
          false := by
      rw [outputSelector]
      exact decide_eq_false notSecondCycle
    have paired := pairedInputCycles_of_firstHalf groups delay positive cycle
      firstHalfCycle
    have firstCycle : pair.1 = cycle := paired.1
    have secondValue : pair.2.val = cycle.val + delay := paired.2
    have currentInput : inputs.get ⟨delay + cycle.val, by
          dsimp only [inputs]
          rw [frameExecutionInputs_length]
          omega⟩ = frame pair.2 := by
      dsimp only [inputs]
      have fetched := frameExecutionInputs_get_frame groups delay frame
        continuation pair.2
      have positionEqual : delay + cycle.val = pair.2.val := by omega
      simpa only [positionEqual] using fetched
    rw [outputFalse, currentInput] at mux
    simp only [Bool.false_eq_true, ↓reduceIte] at mux
    have firstOutput := frame_firstOutput groups delay positive state frame
      continuation cycle
    have firstInput := frame_firstInput groups delay groupsPositive positive state
      frame continuation starts cycle
    dsimp only at firstInput
    rw [if_pos firstHalf] at firstInput
    have firstOutputValue := firstOutput.trans firstInput
    rw [mux, firstOutputValue]
    unfold scheduledOperands
    dsimp only
    rw [if_pos firstHalfCycle]
    rw [firstCycle]
  · have secondHalf : delay ≤ coordinate.2.val := by omega
    have secondHalfCycle :
        delay ≤ (frameCoordinate groups delay cycle).2.val := by
      simpa [coordinate] using secondHalf
    have notFirstHalfCycle :
        ¬(frameCoordinate groups delay cycle).2.val < delay := by omega
    have outputTrue :
        (frameSignal groups delay positive state frame continuation cycle).firstHalf =
          true := by
      rw [outputSelector]
      exact decide_eq_true secondHalfCycle
    have paired := pairedInputCycles_of_secondHalf groups delay positive cycle
      notFirstHalfCycle
    have secondCycle : pair.2 = cycle := paired.1
    have firstValue : pair.1.val + delay = cycle.val := paired.2
    rw [outputTrue] at mux
    simp only [↓reduceIte] at mux
    have finalFirstOutput := frame_firstOutput groups delay positive state frame
      continuation cycle
    have finalFirstInput := frame_firstInput groups delay groupsPositive positive
      state frame continuation starts cycle
    dsimp only at finalFirstInput
    rw [if_neg firstHalf] at finalFirstInput
    have finalFirstValue := finalFirstOutput.trans finalFirstInput
    have currentSecondOutput := frame_secondOutput groups delay positive state frame
      continuation cycle
    have currentSecondInput := frame_secondInput groups delay groupsPositive positive
      state frame continuation starts cycle
    dsimp only at currentSecondInput
    rw [if_neg firstHalf] at currentSecondInput
    have currentSecondValue := currentSecondOutput.trans currentSecondInput
    have earlierSignal :
        (visibleAt delay positive state inputs cycle.val (by
          dsimp only [inputs]
          rw [frameExecutionInputs_length]
          omega)).secondOutput =
          (frameSignal groups delay positive state frame continuation pair.1).secondOutput := by
      have positionEqual : cycle.val = delay + pair.1.val := by omega
      dsimp only [inputs]
      simp only [frameSignal, positionEqual]
    have earlierCoordinate :
        (frameCoordinate groups delay pair.1).2.val =
          coordinate.2.val - delay := by
      let earlierLocal : Fin (2 * delay) :=
        ⟨coordinate.2.val - delay, by
          have phaseLt := coordinate.2.isLt
          omega⟩
      have coordinateEqual :
          frameCoordinate groups delay pair.1 =
            (coordinate.1, earlierLocal) := by
        dsimp only [pair]
        unfold pairedInputCycles
        rw [dif_neg notFirstHalfCycle]
        exact (frameCoordinate groups delay).apply_symm_apply
          (coordinate.1, earlierLocal)
      simpa [earlierLocal] using congrArg (fun value => value.2.val)
        coordinateEqual
    have earlierFirstHalf :
        (frameCoordinate groups delay pair.1).2.val < delay := by
      rw [earlierCoordinate]
      have phaseLt := coordinate.2.isLt
      omega
    have earlierSecondOutput := frame_secondOutput groups delay positive state frame
      continuation pair.1
    have earlierSecondInput := frame_secondInput groups delay groupsPositive positive
      state frame continuation starts pair.1
    dsimp only at earlierSecondInput
    rw [if_pos earlierFirstHalf] at earlierSecondInput
    have firstOperandValue := currentSecondValue.trans
      (earlierSignal.trans (earlierSecondOutput.trans earlierSecondInput))
    rw [mux, firstOperandValue, finalFirstValue]
    unfold scheduledOperands
    dsimp only
    rw [if_neg notFirstHalfCycle]
    rw [secondCycle]

end Commutator

namespace CommutatorBank

/-- A valid bank frame projects to a valid frame on every lane because the
marker is shared. -/
theorem lane_starts
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay)
    (frame : Fin (groups * (2 * delay)) → Input lanes α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input lanes α => input.first = true) frame)
    (lane : Fin lanes) :
    FramedLatency.Starts (by positivity)
      (fun input : Commutator.Input α => input.first = true)
      (fun cycle => laneInput (frame cycle) lane) := by
  constructor
  · exact starts.first
  · intro offset nonzero marked
    exact starts.not_first offset nonzero marked

/-- Every lane of the parallel bank presents its exact stateless operand pair
throughout the complete output frame. -/
theorem frame_operands
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay) (state : State lanes delay α)
    (frame : Fin (groups * (2 * delay)) → Input lanes α)
    (continuation : Fin delay → Input lanes α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input lanes α => input.first = true) frame)
    (cycle : Fin (groups * (2 * delay))) (lane : Fin lanes) :
    (frameSignal groups delay positive state frame continuation cycle lane).operands =
      Commutator.scheduledOperands groups delay positive
        (fun inputCycle => laneInput (frame inputCycle) lane) cycle := by
  exact Commutator.frame_operands groups delay groupsPositive positive
    (state lane) (fun inputCycle => laneInput (frame inputCycle) lane)
    (fun continuationCycle => laneInput (continuation continuationCycle) lane)
    (lane_starts groups delay groupsPositive positive frame starts lane) cycle

/-- Output-period control is likewise common and exact on every lane. -/
theorem frame_outputPhase
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay) (state : State lanes delay α)
    (frame : Fin (groups * (2 * delay)) → Input lanes α)
    (continuation : Fin delay → Input lanes α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input lanes α => input.first = true) frame)
    (cycle : Fin (groups * (2 * delay))) (lane : Fin lanes) :
    (frameSignal groups delay positive state frame continuation cycle lane).outputPhase =
      Commutator.scheduledPhase groups delay cycle := by
  exact Commutator.frame_outputPhase groups delay groupsPositive positive
    (state lane) (fun inputCycle => laneInput (frame inputCycle) lane)
    (fun continuationCycle => laneInput (continuation continuationCycle) lane)
    (lane_starts groups delay groupsPositive positive frame starts lane) cycle

/-- The marker attached to a bank result is the marker from the corresponding
frame-relative input cycle. -/
theorem frame_delayedFirst
    (groups delay : Nat) (positive : 0 < delay)
    (state : State lanes delay α)
    (frame : Fin (groups * (2 * delay)) → Input lanes α)
    (continuation : Fin delay → Input lanes α)
    (cycle : Fin (groups * (2 * delay))) (lane : Fin lanes) :
    (frameSignal groups delay positive state frame continuation cycle lane).delayedFirst =
      (frame cycle).first := by
  exact Commutator.frame_delayedFirst groups delay positive (state lane)
    (fun inputCycle => laneInput (frame inputCycle) lane)
    (fun continuationCycle => laneInput (continuation continuationCycle) lane)
    cycle

/-- Once the pair delay has elapsed, arbitrary prior phase and delay contents
cannot affect any operand in the marked frame's output window. -/
theorem frame_operands_state_independent
    (groups delay : Nat) (groupsPositive : 0 < groups)
    (positive : 0 < delay) (left right : State lanes delay α)
    (frame : Fin (groups * (2 * delay)) → Input lanes α)
    (continuation : Fin delay → Input lanes α)
    (starts : FramedLatency.Starts (by positivity)
      (fun input : Input lanes α => input.first = true) frame)
    (cycle : Fin (groups * (2 * delay))) (lane : Fin lanes) :
    (frameSignal groups delay positive left frame continuation cycle lane).operands =
      (frameSignal groups delay positive right frame continuation cycle lane).operands := by
  rw [frame_operands groups delay groupsPositive positive left frame continuation
      starts cycle lane,
    frame_operands groups delay groupsPositive positive right frame continuation
      starts cycle lane]

end CommutatorBank

/-! ## Physical stage geometry bridge -/

/-- Reindexing a physical marked frame into the generic commutator schedule
preserves its marker protocol. -/
theorem bankFrame_starts
    (geometry : Geometry depth)
    (first : Fin geometry.frameLength → Bool)
    (data : Fin geometry.frameLength → Fin geometry.laneCount → α)
    (starts : FramedLatency.Starts geometry.frameLength_pos
      (fun cycleFirst : Bool => cycleFirst = true) first) :
    FramedLatency.Starts (by
      have groupsPositive : 0 < geometry.outputBoundary.groupCount := by
        simp [BoundaryGeometry.groupCount]
      have pairPositive := Geometry.pairDelay_pos geometry
      exact Nat.mul_pos groupsPositive (Nat.mul_pos (by decide) pairPositive))
      (fun input : CommutatorBank.Input (butterflyCount geometry) α =>
        input.first = true)
      (bankFrame geometry first data) := by
  constructor
  · let scheduleZero : Fin
        (geometry.outputBoundary.groupCount * (2 * geometry.pairDelay)) :=
        ⟨0, by
          exact Nat.mul_pos (by simp [BoundaryGeometry.groupCount])
            (Nat.mul_pos (by decide) (Geometry.pairDelay_pos geometry))⟩
    change first ((Geometry.scheduleCycleEquiv geometry).symm scheduleZero) = true
    have zeroEqual : (Geometry.scheduleCycleEquiv geometry).symm scheduleZero =
        ⟨0, geometry.frameLength_pos⟩ := by
      apply Fin.ext
      rfl
    rw [zeroEqual]
    exact starts.first
  · intro cycle nonzero marked
    let physicalCycle := (Geometry.scheduleCycleEquiv geometry).symm cycle
    have physicalNonzero : physicalCycle.val ≠ 0 := by
      dsimp only [physicalCycle]
      rw [Geometry.scheduleCycleEquiv_symm_val]
      exact nonzero
    apply starts.not_first physicalCycle physicalNonzero
    exact marked

@[simp] theorem outputBoundary_laneEquiv_outputLane
    (geometry : Geometry depth) (branch : Fin 2)
    (lane : Fin (butterflyCount geometry)) :
    geometry.outputBoundary.laneEquiv (outputLane geometry branch lane) =
      (branch, lane) := by
  exact geometry.outputBoundary.laneEquiv.apply_symm_apply (branch, lane)

@[simp] theorem outputLane_outputBoundary_laneEquiv
    (geometry : Geometry depth) (lane : Fin geometry.laneCount) :
    outputLane geometry (geometry.outputBoundary.laneEquiv lane).1
        (geometry.outputBoundary.laneEquiv lane).2 = lane := by
  exact geometry.outputBoundary.laneEquiv.symm_apply_apply lane

/-- The directly decoded physical output coordinate is the same logical
butterfly position as the explicit group/branch/period/lane construction. -/
theorem outputPosition_outputLane
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength)
    (branch : Fin 2) (lane : Fin (butterflyCount geometry)) :
    outputPosition geometry cycle (outputLane geometry branch lane) =
      scheduledPosition geometry cycle branch lane := by
  apply (HTFFT.Exact.layerIndexEquiv depth geometry.stage).injective
  apply Fin.ext
  rw [layerIndexEquiv_outputPosition]
  simp only [HTFFT.Exact.layerIndexEquiv_val,
    BoundaryGeometry.layout_val]
  simp only [outputLane, scheduledPosition,
    outputOffsetsPerBranch_eq_layerOffsets]
  rw [geometry.outputBoundary.laneEquiv.apply_symm_apply]
  rfl

@[simp] theorem outputPosition_outputLane_branch
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength)
    (branch : Fin 2) (lane : Fin (butterflyCount geometry)) :
    (outputPosition geometry cycle (outputLane geometry branch lane)).branch =
      branch := by
  rw [outputPosition_outputLane]
  rfl

/-- Twiddle-table address in arithmetic form: low bank lane plus the
butterfly-count stride times the output-period position. -/
theorem outputPosition_outputLane_offset_val
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength)
    (branch : Fin 2) (lane : Fin (butterflyCount geometry)) :
    (outputPosition geometry cycle (outputLane geometry branch lane)).offset.val =
      lane.val + butterflyCount geometry *
        (geometry.outputBoundary.cycleEquiv cycle).2.val := by
  rw [outputPosition_outputLane]
  rfl

/-- The generic commutator's output-period phase is exactly the batch
coordinate of the physical output boundary. -/
theorem scheduledPhase_val_eq_outputBatch
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength) :
    (Commutator.scheduledPhase geometry.outputBoundary.groupCount
      geometry.pairDelay
      (Geometry.scheduleCycleEquiv geometry cycle)).val =
      (geometry.outputBoundary.cycleEquiv cycle).2.val := by
  change cycle.val % (2 * geometry.pairDelay) =
    cycle.val % geometry.localPeriod
  rw [Geometry.localPeriod_eq_commutatorPeriod geometry]

/-- Consequently, the delayed phase counter and low bank lane select exactly
the twiddle required by the logical butterfly position, independently of the
physical result branch. -/
theorem scheduledTwiddleAddress_eq_outputPosition
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength)
    (branch : Fin 2) (lane : Fin (butterflyCount geometry)) :
    scheduledTwiddleAddress geometry cycle lane =
      (outputPosition geometry cycle (outputLane geometry branch lane)).offset := by
  apply Fin.ext
  rw [outputPosition_outputLane_offset_val]
  change lane.val + butterflyCount geometry *
      (Commutator.scheduledPhase geometry.outputBoundary.groupCount
        geometry.pairDelay
        (Geometry.scheduleCycleEquiv geometry cycle)).val =
    lane.val + butterflyCount geometry *
      (geometry.outputBoundary.cycleEquiv cycle).2.val
  rw [scheduledPhase_val_eq_outputBatch]

/-- Direct input-boundary decomposition names exactly the natural logical
input of the selected butterfly branch. -/
theorem layoutInputCoordinate_eq_inputCoordinate
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry))
    (outputBranch inputBranch : Fin 2) :
    layoutInputCoordinate geometry cycle lane inputBranch =
      inputCoordinate geometry cycle (outputLane geometry outputBranch lane)
        inputBranch := by
  apply geometry.inputBoundary.layout.injective
  rw [inputBoundary_layout_inputCoordinate]
  rw [outputPosition_outputLane]
  simp only [layoutInputCoordinate]
  apply Fin.ext
  rw [BoundaryGeometry.layout_val,
    HTFFT.Exact.layerIndexEquiv_val]
  rw [geometry.inputBoundary.cycleEquiv.apply_symm_apply,
    geometry.inputBoundary.laneEquiv.apply_symm_apply]
  simp only [scheduledPosition, Fin.val_cast]
  let outputCycle := geometry.outputBoundary.cycleEquiv cycle
  let phase := outputPhaseEquiv geometry outputCycle.2
  have phaseValue : outputCycle.2.val =
      phase.2.val + geometry.pairDelay * phase.1.val := by
    exact (Nat.mod_add_div outputCycle.2.val geometry.pairDelay).symm
  have groupValue : (inputGroup geometry outputCycle.1 inputBranch).val =
      inputBranch.val + 2 * outputCycle.1.val := by
    rfl
  have inputOffset : geometry.pairDelay * butterflyCount geometry =
      geometry.inputBoundary.offsetsPerBranch := by
    rw [← geometry.inputBoundary.batchCount_mul_lanesPerBranch]
    rfl
  have outputOffset : 2 * geometry.inputBoundary.offsetsPerBranch =
      2 ^ geometry.stage.val := by
    calc
      2 * geometry.inputBoundary.offsetsPerBranch =
          2 * (geometry.pairDelay * butterflyCount geometry) := by
        rw [inputOffset]
      _ = (2 * geometry.pairDelay) * butterflyCount geometry := by ring
      _ = geometry.localPeriod * butterflyCount geometry := by
        rw [Geometry.localPeriod_eq_commutatorPeriod geometry]
      _ = geometry.outputBoundary.offsetsPerBranch := by
        rw [← geometry.outputBoundary.batchCount_mul_lanesPerBranch]
        rfl
      _ = 2 ^ geometry.stage.val :=
        outputOffsetsPerBranch_eq_layerOffsets geometry
  change lane.val + butterflyCount geometry * phase.2.val +
        geometry.inputBoundary.offsetsPerBranch * phase.1.val +
        (2 * geometry.inputBoundary.offsetsPerBranch) *
          (inputGroup geometry outputCycle.1 inputBranch).val =
      lane.val + butterflyCount geometry * outputCycle.2.val +
        2 ^ geometry.stage.val * inputBranch.val +
        (2 * 2 ^ geometry.stage.val) * outputCycle.1.val
  rw [phaseValue, groupValue, ← outputOffset, ← inputOffset]
  ring

/-- Numerical cycle selected by the direct input-layout decomposition. -/
theorem layoutInputCoordinate_cycle_val
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) (branch : Fin 2) :
    (layoutInputCoordinate geometry cycle lane branch).1.val =
      let outputCycle := geometry.outputBoundary.cycleEquiv cycle
      let phase := outputPhaseEquiv geometry outputCycle.2
      phase.2.val + geometry.pairDelay *
        (branch.val + 2 * outputCycle.1.val) := by
  rfl

/-- Lane decomposition selected by the direct input-layout coordinate. -/
theorem inputLaneEquiv_layoutInputCoordinate
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) (branch : Fin 2) :
    geometry.inputBoundary.laneEquiv
        (layoutInputCoordinate geometry cycle lane branch).2 =
      let outputCycle := geometry.outputBoundary.cycleEquiv cycle
      let phase := outputPhaseEquiv geometry outputCycle.2
      (phase.1, lane) := by
  simp [layoutInputCoordinate]
  rfl

/-- Numerical cycle selected by the generic paired-input schedule. -/
theorem scheduledInputCoordinate_cycle_val
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) (branch : Fin 2) :
    (scheduledInputCoordinate geometry cycle lane branch).1.val =
      let scheduleCycle := Geometry.scheduleCycleEquiv geometry cycle
      let pair := Commutator.pairedInputCycles
        geometry.outputBoundary.groupCount geometry.pairDelay
        (Geometry.pairDelay_pos geometry) scheduleCycle
      if branch = 0 then pair.1.val else pair.2.val := by
  by_cases zero : branch = 0 <;>
    simp [scheduledInputCoordinate, zero,
      Geometry.scheduleCycleEquiv_symm_val]

/-- Lane decomposition selected by the generic paired-input schedule. -/
theorem inputLaneEquiv_scheduledInputCoordinate
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) (branch : Fin 2) :
    geometry.inputBoundary.laneEquiv
        (scheduledInputCoordinate geometry cycle lane branch).2 =
      let scheduleCycle := Geometry.scheduleCycleEquiv geometry cycle
      let phase := Commutator.scheduledPhase
        geometry.outputBoundary.groupCount geometry.pairDelay scheduleCycle
      (if phase.val < geometry.pairDelay then 0 else 1, lane) := by
  simp [scheduledInputCoordinate]
  rfl

/-- The generic paired-cycle schedule and the direct boundary-layout
decomposition select the same physical input coordinate. -/
theorem scheduledInputCoordinate_eq_layoutInputCoordinate
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) (branch : Fin 2) :
    scheduledInputCoordinate geometry cycle lane branch =
      layoutInputCoordinate geometry cycle lane branch := by
  let scheduleCycle := Geometry.scheduleCycleEquiv geometry cycle
  let scheduleCoordinate := Commutator.frameCoordinate
    geometry.outputBoundary.groupCount geometry.pairDelay scheduleCycle
  let outputCycle := geometry.outputBoundary.cycleEquiv cycle
  let phase := outputPhaseEquiv geometry outputCycle.2
  let pair := Commutator.pairedInputCycles
    geometry.outputBoundary.groupCount geometry.pairDelay
    (Geometry.pairDelay_pos geometry) scheduleCycle
  have groupValue : scheduleCoordinate.1.val = outputCycle.1.val := by
    change cycle.val / (2 * geometry.pairDelay) =
      cycle.val / geometry.localPeriod
    rw [Geometry.localPeriod_eq_commutatorPeriod geometry]
  have periodValue : scheduleCoordinate.2.val = outputCycle.2.val := by
    exact scheduledPhase_val_eq_outputBatch geometry cycle
  have scheduleValue : scheduleCycle.val = scheduleCoordinate.2.val +
      (2 * geometry.pairDelay) * scheduleCoordinate.1.val := by
    exact (Nat.mod_add_div scheduleCycle.val
      (2 * geometry.pairDelay)).symm
  have scheduleValueOutput : scheduleCycle.val = scheduleCoordinate.2.val +
      geometry.pairDelay * (2 * outputCycle.1.val) := by
    rw [scheduleValue, groupValue]
    ring
  have phaseFirstValue : phase.1.val =
      outputCycle.2.val / geometry.pairDelay := by
    rfl
  have phaseSecondValue : phase.2.val =
      outputCycle.2.val % geometry.pairDelay := by
    rfl
  apply Prod.ext
  · apply Fin.ext
    rw [scheduledInputCoordinate_cycle_val,
      layoutInputCoordinate_cycle_val]
    change (if branch = 0 then pair.1.val else pair.2.val) =
      phase.2.val + geometry.pairDelay *
        (branch.val + 2 * outputCycle.1.val)
    by_cases firstHalf : scheduleCoordinate.2.val < geometry.pairDelay
    · have paired := Commutator.pairedInputCycles_of_firstHalf
        geometry.outputBoundary.groupCount geometry.pairDelay
        (Geometry.pairDelay_pos geometry) scheduleCycle firstHalf
      have phaseFirst : phase.1.val = 0 := by
        rw [phaseFirstValue, ← periodValue]
        exact Nat.div_eq_of_lt firstHalf
      have phaseSecond : phase.2.val = scheduleCoordinate.2.val := by
        rw [phaseSecondValue, ← periodValue]
        exact Nat.mod_eq_of_lt firstHalf
      have pairFirst : pair.1.val = scheduleCycle.val := by
        exact congrArg Fin.val paired.1
      have pairSecond : pair.2.val =
          scheduleCycle.val + geometry.pairDelay := paired.2
      by_cases branchZero : branch = 0
      · have branchValue : branch.val = 0 := congrArg Fin.val branchZero
        rw [if_pos branchZero, pairFirst, phaseSecond, branchValue,
          scheduleValueOutput]
        ring
      · have branchValue : branch.val = 1 := by
          have branchLt := branch.isLt
          omega
        rw [if_neg branchZero, pairSecond, phaseSecond, branchValue,
          scheduleValueOutput]
        ring
    · have paired := Commutator.pairedInputCycles_of_secondHalf
        geometry.outputBoundary.groupCount geometry.pairDelay
        (Geometry.pairDelay_pos geometry) scheduleCycle firstHalf
      have phaseGe : geometry.pairDelay ≤ scheduleCoordinate.2.val := by
        omega
      have phaseLt : scheduleCoordinate.2.val < 2 * geometry.pairDelay :=
        scheduleCoordinate.2.isLt
      have phaseFirst : phase.1.val = 1 := by
        rw [phaseFirstValue, ← periodValue]
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      have phaseSecond : phase.2.val =
          scheduleCoordinate.2.val - geometry.pairDelay := by
        have decomposition := Nat.mod_add_div scheduleCoordinate.2.val
          geometry.pairDelay
        have quotient : scheduleCoordinate.2.val / geometry.pairDelay = 1 :=
          Nat.div_eq_of_lt_le (by omega) (by omega)
        calc
          phase.2.val = scheduleCoordinate.2.val % geometry.pairDelay := by
            rw [phaseSecondValue, ← periodValue]
          _ = scheduleCoordinate.2.val - geometry.pairDelay := by
            rw [quotient] at decomposition
            omega
      have pairSecond : pair.2.val = scheduleCycle.val := by
        exact congrArg Fin.val paired.1
      have pairFirst : pair.1.val + geometry.pairDelay =
          scheduleCycle.val := paired.2
      by_cases branchZero : branch = 0
      · have branchValue : branch.val = 0 := congrArg Fin.val branchZero
        rw [if_pos branchZero, phaseSecond, branchValue]
        simp only [Nat.zero_add]
        have targetPlus :
            (scheduleCoordinate.2.val - geometry.pairDelay +
                geometry.pairDelay * (2 * outputCycle.1.val)) +
              geometry.pairDelay = scheduleCycle.val := by
          rw [scheduleValueOutput]
          omega
        omega
      · have branchValue : branch.val = 1 := by
          have branchLt := branch.isLt
          omega
        rw [if_neg branchZero, pairSecond, phaseSecond, branchValue,
          scheduleValueOutput]
        have sum : geometry.pairDelay * (1 + 2 * outputCycle.1.val) =
            geometry.pairDelay +
              geometry.pairDelay * (2 * outputCycle.1.val) := by ring
        rw [sum]
        omega
  · apply geometry.inputBoundary.laneEquiv.injective
    rw [inputLaneEquiv_scheduledInputCoordinate,
      inputLaneEquiv_layoutInputCoordinate]
    change (if scheduleCoordinate.2.val < geometry.pairDelay then 0 else 1,
      lane) = (phase.1, lane)
    by_cases firstHalf : scheduleCoordinate.2.val < geometry.pairDelay
    · have phaseFirst : phase.1 = 0 := by
        apply Fin.ext
        rw [phaseFirstValue, ← periodValue]
        exact Nat.div_eq_of_lt firstHalf
      rw [if_pos firstHalf, phaseFirst]
    · have phaseGe : geometry.pairDelay ≤ scheduleCoordinate.2.val := by
        omega
      have phaseLt : scheduleCoordinate.2.val < 2 * geometry.pairDelay :=
        scheduleCoordinate.2.isLt
      have phaseFirst : phase.1 = 1 := by
        apply Fin.ext
        rw [phaseFirstValue, ← periodValue]
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [if_neg firstHalf, phaseFirst]

/-- The generic paired-input schedule therefore selects exactly the natural
logical input coordinate of either butterfly branch. -/
theorem scheduledInputCoordinate_eq_inputCoordinate
    (geometry : Geometry depth) (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry))
    (outputBranch inputBranch : Fin 2) :
    scheduledInputCoordinate geometry cycle lane inputBranch =
      inputCoordinate geometry cycle (outputLane geometry outputBranch lane)
        inputBranch :=
  (scheduledInputCoordinate_eq_layoutInputCoordinate geometry cycle lane
    inputBranch).trans
      (layoutInputCoordinate_eq_inputCoordinate geometry cycle lane
        outputBranch inputBranch)

/-- Splitting the physical input lanes and applying the generic paired-cycle
schedule reads the two values at the corresponding scheduled coordinates. -/
theorem scheduledOperands_bankFrame
    (geometry : Geometry depth)
    (first : Fin geometry.frameLength → Bool)
    (data : Fin geometry.frameLength → Fin geometry.laneCount → α)
    (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) :
    Commutator.scheduledOperands geometry.outputBoundary.groupCount
        geometry.pairDelay (Geometry.pairDelay_pos geometry)
        (fun inputCycle => CommutatorBank.laneInput
          (bankFrame geometry first data inputCycle) lane)
        (Geometry.scheduleCycleEquiv geometry cycle) =
      { a := data (scheduledInputCoordinate geometry cycle lane 0).1
          (scheduledInputCoordinate geometry cycle lane 0).2
        b := data (scheduledInputCoordinate geometry cycle lane 1).1
          (scheduledInputCoordinate geometry cycle lane 1).2 } := by
  unfold Commutator.scheduledOperands
  let scheduleCycle := Geometry.scheduleCycleEquiv geometry cycle
  let coordinate := Commutator.frameCoordinate
    geometry.outputBoundary.groupCount geometry.pairDelay scheduleCycle
  by_cases firstHalf : coordinate.2.val < geometry.pairDelay
  · rw [if_pos firstHalf]
    have scheduledFirstHalf :
        (Commutator.scheduledPhase geometry.outputBoundary.groupCount
          geometry.pairDelay
          (Geometry.scheduleCycleEquiv geometry cycle)).val <
            geometry.pairDelay := firstHalf
    simp [bankFrame, bankInput, CommutatorBank.laneInput,
      scheduledInputCoordinate, scheduledFirstHalf]
  · rw [if_neg firstHalf]
    have scheduledSecondHalf :
        ¬(Commutator.scheduledPhase geometry.outputBoundary.groupCount
          geometry.pairDelay
          (Geometry.scheduleCycleEquiv geometry cycle)).val <
            geometry.pairDelay := firstHalf
    simp [bankFrame, bankInput, CommutatorBank.laneInput,
      scheduledInputCoordinate, scheduledSecondHalf]

/-- Stateless bank operands are exactly the two natural logical inputs of the
butterfly, for either physical output branch. -/
theorem scheduledOperands_bankFrame_eq_inputCoordinates
    (geometry : Geometry depth)
    (first : Fin geometry.frameLength → Bool)
    (data : Fin geometry.frameLength → Fin geometry.laneCount → α)
    (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) (outputBranch : Fin 2) :
    Commutator.scheduledOperands geometry.outputBoundary.groupCount
        geometry.pairDelay (Geometry.pairDelay_pos geometry)
        (fun inputCycle => CommutatorBank.laneInput
          (bankFrame geometry first data inputCycle) lane)
        (Geometry.scheduleCycleEquiv geometry cycle) =
      { a := data
          (inputCoordinate geometry cycle
            (outputLane geometry outputBranch lane) 0).1
          (inputCoordinate geometry cycle
            (outputLane geometry outputBranch lane) 0).2
        b := data
          (inputCoordinate geometry cycle
            (outputLane geometry outputBranch lane) 1).1
          (inputCoordinate geometry cycle
            (outputLane geometry outputBranch lane) 1).2 } := by
  rw [scheduledOperands_bankFrame geometry first data cycle lane,
    scheduledInputCoordinate_eq_inputCoordinate geometry cycle lane
      outputBranch 0,
    scheduledInputCoordinate_eq_inputCoordinate geometry cycle lane
      outputBranch 1]

/-- Complete pure commutator-bank correctness over the physical stage
geometry.  Every state and continuation are allowed; the marked frame alone
determines all operands beginning exactly `pairDelay` cycles later. -/
theorem bankFrame_operands_eq_inputCoordinates
    (geometry : Geometry depth)
    (first : Fin geometry.frameLength → Bool)
    (data : Fin geometry.frameLength → Fin geometry.laneCount → α)
    (state : CommutatorBank.State (butterflyCount geometry)
      geometry.pairDelay α)
    (continuation : Fin geometry.pairDelay →
      CommutatorBank.Input (butterflyCount geometry) α)
    (starts : FramedLatency.Starts geometry.frameLength_pos
      (fun cycleFirst : Bool => cycleFirst = true) first)
    (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) (outputBranch : Fin 2) :
    (CommutatorBank.frameSignal geometry.outputBoundary.groupCount
      geometry.pairDelay (Geometry.pairDelay_pos geometry) state
      (bankFrame geometry first data) continuation
      (Geometry.scheduleCycleEquiv geometry cycle) lane).operands =
      { a := data
          (inputCoordinate geometry cycle
            (outputLane geometry outputBranch lane) 0).1
          (inputCoordinate geometry cycle
            (outputLane geometry outputBranch lane) 0).2
        b := data
          (inputCoordinate geometry cycle
            (outputLane geometry outputBranch lane) 1).1
          (inputCoordinate geometry cycle
            (outputLane geometry outputBranch lane) 1).2 } := by
  have groupsPositive : 0 < geometry.outputBoundary.groupCount := by
    simp [BoundaryGeometry.groupCount]
  rw [CommutatorBank.frame_operands geometry.outputBoundary.groupCount
      geometry.pairDelay groupsPositive (Geometry.pairDelay_pos geometry)
      state (bankFrame geometry first data) continuation
      (bankFrame_starts geometry first data starts)
      (Geometry.scheduleCycleEquiv geometry cycle) lane]
  exact scheduledOperands_bankFrame_eq_inputCoordinates geometry first data
    cycle lane outputBranch

/-- The pure bank propagates the frame marker to the operand boundary with
exactly the same frame-relative position. -/
theorem bankFrame_delayedFirst
    (geometry : Geometry depth)
    (first : Fin geometry.frameLength → Bool)
    (data : Fin geometry.frameLength → Fin geometry.laneCount → α)
    (state : CommutatorBank.State (butterflyCount geometry)
      geometry.pairDelay α)
    (continuation : Fin geometry.pairDelay →
      CommutatorBank.Input (butterflyCount geometry) α)
    (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) :
    (CommutatorBank.frameSignal geometry.outputBoundary.groupCount
      geometry.pairDelay (Geometry.pairDelay_pos geometry) state
      (bankFrame geometry first data) continuation
      (Geometry.scheduleCycleEquiv geometry cycle) lane).delayedFirst =
      first cycle := by
  rw [CommutatorBank.frame_delayedFirst]
  rfl

/-- Hence the delayed marker itself satisfies the complete output-frame marker
protocol whenever the physical input marker does. -/
theorem bankFrame_delayedFirst_starts
    (geometry : Geometry depth)
    (first : Fin geometry.frameLength → Bool)
    (data : Fin geometry.frameLength → Fin geometry.laneCount → α)
    (state : CommutatorBank.State (butterflyCount geometry)
      geometry.pairDelay α)
    (continuation : Fin geometry.pairDelay →
      CommutatorBank.Input (butterflyCount geometry) α)
    (starts : FramedLatency.Starts geometry.frameLength_pos
      (fun cycleFirst : Bool => cycleFirst = true) first)
    (lane : Fin (butterflyCount geometry)) :
    FramedLatency.Starts geometry.frameLength_pos
      (fun cycleFirst : Bool => cycleFirst = true)
      (fun cycle =>
        (CommutatorBank.frameSignal geometry.outputBoundary.groupCount
          geometry.pairDelay (Geometry.pairDelay_pos geometry) state
          (bankFrame geometry first data) continuation
          (Geometry.scheduleCycleEquiv geometry cycle) lane).delayedFirst) := by
  have markerEqual :
      (fun cycle =>
        (CommutatorBank.frameSignal geometry.outputBoundary.groupCount
          geometry.pairDelay (Geometry.pairDelay_pos geometry) state
          (bankFrame geometry first data) continuation
          (Geometry.scheduleCycleEquiv geometry cycle) lane).delayedFirst) =
        first := by
    funext cycle
    exact bankFrame_delayedFirst geometry first data state continuation cycle lane
  rw [markerEqual]
  exact starts

/-- The address presented to the twiddle ROM by the delayed bank control is
the exact logical twiddle offset required at that output coordinate. -/
theorem bankFrame_twiddleAddress
    (geometry : Geometry depth)
    (first : Fin geometry.frameLength → Bool)
    (data : Fin geometry.frameLength → Fin geometry.laneCount → α)
    (state : CommutatorBank.State (butterflyCount geometry)
      geometry.pairDelay α)
    (continuation : Fin geometry.pairDelay →
      CommutatorBank.Input (butterflyCount geometry) α)
    (starts : FramedLatency.Starts geometry.frameLength_pos
      (fun cycleFirst : Bool => cycleFirst = true) first)
    (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) (outputBranch : Fin 2) :
    twiddleAddress geometry
        (CommutatorBank.frameSignal geometry.outputBoundary.groupCount
          geometry.pairDelay (Geometry.pairDelay_pos geometry) state
          (bankFrame geometry first data) continuation
          (Geometry.scheduleCycleEquiv geometry cycle) lane).outputPhase lane =
      (outputPosition geometry cycle
        (outputLane geometry outputBranch lane)).offset := by
  have groupsPositive : 0 < geometry.outputBoundary.groupCount := by
    simp [BoundaryGeometry.groupCount]
  rw [CommutatorBank.frame_outputPhase geometry.outputBoundary.groupCount
      geometry.pairDelay groupsPositive (Geometry.pairDelay_pos geometry)
      state (bankFrame geometry first data) continuation
      (bankFrame_starts geometry first data starts)
      (Geometry.scheduleCycleEquiv geometry cycle) lane]
  exact scheduledTwiddleAddress_eq_outputPosition geometry cycle outputBranch lane

/-- Evaluating the pure commutator observations through the natural butterfly
and twiddle functions produces the already approved physical scheduled frame. -/
theorem outputFrameOfBankFrameSignals_eq_scheduledOutputFrame
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (state : CommutatorBank.State (butterflyCount geometry)
      geometry.pairDelay
      ((complexSignalType
        (configuration.boundaryFormat geometry.stage.castSucc)).Denote))
    (first : Fin geometry.frameLength → Bool)
    (input : InputFrame configuration geometry)
    (continuation : Fin geometry.pairDelay →
      CommutatorBank.Input (butterflyCount geometry)
        ((complexSignalType
          (configuration.boundaryFormat geometry.stage.castSucc)).Denote))
    (starts : FramedLatency.Starts geometry.frameLength_pos
      (fun cycleFirst : Bool => cycleFirst = true) first) :
    outputFrameOfBankSignals configuration table geometry
        (bankFrameSignals configuration geometry state first input continuation) =
      scheduledOutputFrame configuration table geometry input := by
  funext cycle physicalLane
  let laneCoordinate := geometry.outputBoundary.laneEquiv physicalLane
  have physicalLaneEqual :
      outputLane geometry laneCoordinate.1 laneCoordinate.2 = physicalLane := by
    exact outputLane_outputBoundary_laneEquiv geometry physicalLane
  rw [← physicalLaneEqual]
  simp only [outputFrameOfBankSignals, scheduledOutputFrame,
    bankFrameSignals]
  rw [outputBoundary_laneEquiv_outputLane]
  let visible := CommutatorBank.frameSignal
    geometry.outputBoundary.groupCount geometry.pairDelay
    (Geometry.pairDelay_pos geometry) state (bankFrame geometry first input)
    continuation (Geometry.scheduleCycleEquiv geometry cycle) laneCoordinate.2
  have operands := bankFrame_operands_eq_inputCoordinates geometry first input
    state continuation starts cycle laneCoordinate.2 laneCoordinate.1
  have operandA := congrArg Commutator.Operands.a operands
  have operandB := congrArg Commutator.Operands.b operands
  have address := bankFrame_twiddleAddress geometry first input state continuation
    starts cycle laneCoordinate.2 laneCoordinate.1
  change visible.operands.a =
    input (inputCoordinate geometry cycle
      (outputLane geometry laneCoordinate.1 laneCoordinate.2) 0).1
      (inputCoordinate geometry cycle
        (outputLane geometry laneCoordinate.1 laneCoordinate.2) 0).2 at operandA
  change visible.operands.b =
    input (inputCoordinate geometry cycle
      (outputLane geometry laneCoordinate.1 laneCoordinate.2) 1).1
      (inputCoordinate geometry cycle
        (outputLane geometry laneCoordinate.1 laneCoordinate.2) 1).2 at operandB
  change twiddleAddress geometry visible.outputPhase laneCoordinate.2 =
    (outputPosition geometry cycle
      (outputLane geometry laneCoordinate.1 laneCoordinate.2)).offset at address
  change
    PipelinedFixedButterfly.encodeComplex
        (configuration.boundaryFormat geometry.stage.succ).width
        (if laneCoordinate.1 = 0 then
          (HTFFT.Butterfly.Fixed.butterfly
            (configuration.fixedConfig.butterfly geometry.stage)
            (PipelinedFixedButterfly.decodeComplex
              (configuration.boundaryFormat geometry.stage.castSucc).width
              visible.operands.a)
            (PipelinedFixedButterfly.decodeComplex
              (configuration.boundaryFormat geometry.stage.castSucc).width
              visible.operands.b)
            (table.value geometry.stage
              (twiddleAddress geometry visible.outputPhase laneCoordinate.2))).upper
        else
          (HTFFT.Butterfly.Fixed.butterfly
            (configuration.fixedConfig.butterfly geometry.stage)
            (PipelinedFixedButterfly.decodeComplex
              (configuration.boundaryFormat geometry.stage.castSucc).width
              visible.operands.a)
            (PipelinedFixedButterfly.decodeComplex
              (configuration.boundaryFormat geometry.stage.castSucc).width
              visible.operands.b)
            (table.value geometry.stage
              (twiddleAddress geometry visible.outputPhase laneCoordinate.2))).lower) = _
  rw [operandA, operandB, address, outputPosition_outputLane_branch]

/-- End-to-end pure scheduling theorem for one stage: the generic bank,
twiddle address, and butterfly evaluation realize the public natural stage
result, before introducing any Silean structure. -/
theorem outputFrameOfBankFrameSignals_eq_contractResult
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (state : CommutatorBank.State (butterflyCount geometry)
      geometry.pairDelay
      ((complexSignalType
        (configuration.boundaryFormat geometry.stage.castSucc)).Denote))
    (first : Fin geometry.frameLength → Bool)
    (input : InputFrame configuration geometry)
    (continuation : Fin geometry.pairDelay →
      CommutatorBank.Input (butterflyCount geometry)
        ((complexSignalType
          (configuration.boundaryFormat geometry.stage.castSucc)).Denote))
    (starts : FramedLatency.Starts geometry.frameLength_pos
      (fun cycleFirst : Bool => cycleFirst = true) first) :
    outputFrameOfBankSignals configuration table geometry
        (bankFrameSignals configuration geometry state first input continuation) =
      encodeOutputFrame configuration geometry
        (resultValue configuration table geometry input) := by
  rw [outputFrameOfBankFrameSignals_eq_scheduledOutputFrame configuration table
      geometry state first input continuation starts,
    scheduledOutputFrame_eq_contractResult]

end HTFFT.Silean.FFTStage.Internal
