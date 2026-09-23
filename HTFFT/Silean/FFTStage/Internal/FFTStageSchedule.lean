import HTFFT.Silean.FFTStage.FFTStage
import Silean.Semantics.DelayLine

/-! # Pure schedule for the shift-register streaming FFT stage

This file describes the control and commutator independently of Silean
instances.  For a positive delay `D`, two `D`-cycle delay lines transform the
two physical lane halves as follows:

```text
phase         delay₁ input   delay₂ input   butterfly operands
first half    current A      current B      delay₂ out, delay₁ out
second half   current B      delay₂ out     delay₁ out, current A
```

The first constrained butterfly invocation is `D` cycles after `i_first`.
Second-half invocations emit the low-offset half of an output period; the next
first-half invocations emit its high-offset half.  `i_first` selects phase zero
for the current cycle and phase one for the following cycle, irrespective of
the previously stored phase.  Delay contents are deliberately not reset.
-/

namespace HTFFT.Silean.FFTStage.Internal

open _root_.Silean

namespace DelayLine

/-- Pure state of a positive-latency shift register.  Index zero is the value
observed next; increasing indices move toward the input.  This is the same
orientation used by `Silean.DelayLine.Step`. -/
abbrev State (delay : Nat) (α : Type u) := Fin delay → α

/-- Value visible from a positive delay line in the current cycle. -/
def output (delay : Nat) (positive : 0 < delay)
    (state : State delay α) : α :=
  state ⟨0, positive⟩

/-- State after shifting one new value into a positive delay line. -/
def next (delay : Nat) (input : α) (state : State delay α) : State delay α :=
  fun index =>
    if earlier : index.val + 1 < delay then
      state ⟨index.val + 1, earlier⟩
    else
      input

/-- One functional shift is an instance of the shared abstract delay-line
step relation.  Keeping this bridge at the pure schedule boundary lets the
later structural proof reuse `Silean.DelayLine.input_reaches_output`. -/
theorem step (delay : Nat) (positive : 0 < delay)
    (input : α) (state : State delay α) :
    _root_.Silean.DelayLine.Step delay input state
      (output delay positive state) (next delay input state) := by
  constructor
  · simp [output, positive]
  · intro index
    rfl

end DelayLine

namespace Commutator

/-- The shift-register commutator state.  The phase has period `2 * delay`;
the positivity argument used by operations makes that period nonempty. -/
structure State (delay : Nat) (α : Type u) where
  /-- Phase controlling the input commutator switches. -/
  phase : Fin (2 * delay)
  /-- Phase naming the butterfly result produced in the current cycle. -/
  outputPhase : Fin (2 * delay)
  /-- `i_first` delayed to the operand-output boundary. -/
  markerDelay : DelayLine.State delay Bool
  firstDelay : DelayLine.State delay α
  secondDelay : DelayLine.State delay α

/-- Convert an arbitrary natural number to the corresponding periodic phase. -/
def phaseOfNat (delay : Nat) (positive : 0 < delay) (value : Nat) :
    Fin (2 * delay) :=
  ⟨value % (2 * delay), Nat.mod_lt _ (by omega)⟩

/-- `i_first` rephases the marked cycle itself, rather than only the following
cycle. -/
def effectivePhase (delay : Nat) (positive : 0 < delay)
    (stored : Fin (2 * delay)) (first : Bool) : Fin (2 * delay) :=
  if first then phaseOfNat delay positive 0 else stored

/-- A marker can only move the effective phase backward to zero. -/
theorem effectivePhase_val_le (delay : Nat) (positive : 0 < delay)
    (stored : Fin (2 * delay)) (first : Bool) :
    (effectivePhase delay positive stored first).val ≤ stored.val := by
  cases first <;> simp [effectivePhase, phaseOfNat]

/-- Phase stored after the active cycle.  A marked cycle is phase zero, so the
following cycle begins at phase one. -/
def nextPhase (delay : Nat) (positive : 0 < delay)
    (stored : Fin (2 * delay)) (first : Bool) : Fin (2 * delay) :=
  phaseOfNat delay positive
    ((effectivePhase delay positive stored first).val + 1)

/-- One cycle advances the stored phase by at most one; a marker may reset it
to one instead. -/
theorem nextPhase_val_le_succ (delay : Nat) (positive : 0 < delay)
    (stored : Fin (2 * delay)) (first : Bool) :
    (nextPhase delay positive stored first).val ≤ stored.val + 1 := by
  have effectiveLe := effectivePhase_val_le delay positive stored first
  have modLe := Nat.mod_le
    ((effectivePhase delay positive stored first).val + 1) (2 * delay)
  simp only [nextPhase, phaseOfNat, Fin.val_mk]
  omega

/-- Whether the effective phase is in the first half of its local period. -/
def inFirstHalf (delay : Nat) (phase : Fin (2 * delay)) : Bool :=
  decide (phase.val < delay)

/-- Output-period position produced by a butterfly invoked at `phase`.  It is
the current phase with the half-period bit toggled. -/
def outputPhase (delay : Nat) (positive : 0 < delay)
    (phase : Fin (2 * delay)) : Fin (2 * delay) :=
  phaseOfNat delay positive (phase.val + delay)

/-- One pair of physical lane halves entering the commutator. -/
structure Input (α : Type u) where
  first : Bool
  a : α
  b : α

/-- Values presented to one lane of the butterfly bank in the current cycle. -/
structure Operands (α : Type u) where
  a : α
  b : α
deriving DecidableEq, Repr

/-- All combinationally visible values of one commutator cycle.  Exposing
these values in the pure model gives the later structural proof a direct
correspondence target without putting hardware instances into this file. -/
structure Signals (delay : Nat) (α : Type u) where
  phase : Fin (2 * delay)
  delayedFirst : Bool
  outputPhase : Fin (2 * delay)
  firstHalf : Bool
  firstOutput : α
  secondOutput : α
  firstInput : α
  secondInput : α
  operands : Operands α
deriving DecidableEq, Repr

/-- Combinational values selected during one commutator cycle. -/
def signals (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (input : Input α) : Signals delay α :=
  let phase := effectivePhase delay positive state.phase input.first
  let delayedFirst := DelayLine.output delay positive state.markerDelay
  let outputPhase := effectivePhase delay positive state.outputPhase delayedFirst
  let firstHalf := inFirstHalf delay phase
  let firstOutput := DelayLine.output delay positive state.firstDelay
  let secondOutput := DelayLine.output delay positive state.secondDelay
  let operands :=
    if firstHalf then
      { a := secondOutput, b := firstOutput }
    else
      { a := firstOutput, b := input.a }
  let firstInput := if firstHalf then input.a else input.b
  let secondInput := if firstHalf then input.b else secondOutput
  { phase := phase
    delayedFirst := delayedFirst
    outputPhase := outputPhase
    firstHalf := firstHalf
    firstOutput := firstOutput
    secondOutput := secondOutput
    firstInput := firstInput
    secondInput := secondInput
    operands := operands }

/-- State following one commutator cycle. -/
def nextState (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (input : Input α) : State delay α :=
  let visible := signals delay positive state input
  { phase := nextPhase delay positive state.phase input.first
    outputPhase := nextPhase delay positive state.outputPhase visible.delayedFirst
    markerDelay := DelayLine.next delay input.first state.markerDelay
    firstDelay := DelayLine.next delay visible.firstInput state.firstDelay
    secondDelay := DelayLine.next delay visible.secondInput state.secondDelay }

/-- One pure commutator transition. -/
def step (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (input : Input α) : Operands α × State delay α :=
  let visible := signals delay positive state input
  (visible.operands, nextState delay positive state input)

/-- Execute the pure commutator while retaining the internal delay-line and
phase observations needed by its correctness proof. -/
def runDetailed (delay : Nat) (positive : 0 < delay)
    (state : State delay α) :
    List (Input α) → List (Signals delay α) × State delay α
  | [] => ([], state)
  | input :: inputs =>
      let visible := signals delay positive state input
      let next := nextState delay positive state input
      let rest := runDetailed delay positive next inputs
      (visible :: rest.1, rest.2)

/-- A detailed run has exactly one visible signal bundle per input cycle. -/
theorem runDetailed_length (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α)) :
    (runDetailed delay positive state inputs).1.length = inputs.length := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs induction =>
      simp only [runDetailed, List.length_cons]
      rw [induction]

/-- Execute the pure commutator over a finite input trace. -/
def run (delay : Nat) (positive : 0 < delay)
    (state : State delay α) : List (Input α) → List (Operands α) × State delay α
  | inputs =>
      let result := runDetailed delay positive state inputs
      (result.1.map Signals.operands, result.2)

@[simp] theorem effectivePhase_of_first (delay : Nat) (positive : 0 < delay)
    (stored : Fin (2 * delay)) :
    effectivePhase delay positive stored true = phaseOfNat delay positive 0 := by
  simp [effectivePhase]

@[simp] theorem nextPhase_of_first (delay : Nat) (positive : 0 < delay)
    (stored : Fin (2 * delay)) :
    nextPhase delay positive stored true = phaseOfNat delay positive 1 := by
  apply Fin.ext
  simp [nextPhase, effectivePhase, phaseOfNat,
    Nat.mod_eq_of_lt (show 1 < 2 * delay by omega)]

@[simp] theorem effectivePhase_of_not_first
    (delay : Nat) (positive : 0 < delay)
    (stored : Fin (2 * delay)) :
    effectivePhase delay positive stored false = stored := by
  simp [effectivePhase]

/-- Away from a frame marker, a canonical phase advances by one position. -/
@[simp] theorem nextPhase_phaseOfNat_false
    (delay : Nat) (positive : 0 < delay) (value : Nat) :
    nextPhase delay positive (phaseOfNat delay positive value) false =
      phaseOfNat delay positive (value + 1) := by
  apply Fin.ext
  simp [nextPhase, effectivePhase, phaseOfNat, Nat.add_mod]

@[simp] theorem phaseOfNat_add_period (delay : Nat) (positive : 0 < delay)
    (value : Nat) :
    phaseOfNat delay positive (value + 2 * delay) =
      phaseOfNat delay positive value := by
  apply Fin.ext
  simp [phaseOfNat]

/-- Advancing the canonical representative agrees with advancing the
underlying natural-number phase. -/
@[simp] theorem phaseOfNat_phaseOfNat_val_succ
    (delay : Nat) (positive : 0 < delay) (value : Nat) :
    phaseOfNat delay positive ((phaseOfNat delay positive value).val + 1) =
      phaseOfNat delay positive (value + 1) := by
  apply Fin.ext
  simp [phaseOfNat, Nat.add_mod]

/-- Starting from phase `D`, toggling the half-period bit identifies output
position zero.  This is the commutator's fixed latency before the butterfly. -/
@[simp] theorem outputPhase_pairDelay (delay : Nat) (positive : 0 < delay) :
    outputPhase delay positive (phaseOfNat delay positive delay) =
      phaseOfNat delay positive 0 := by
  apply Fin.ext
  simp only [outputPhase, phaseOfNat, Fin.val_mk]
  rw [Nat.mod_eq_of_lt (show delay < 2 * delay by omega)]
  rw [show delay + delay = 2 * delay by omega, Nat.mod_self]
  simp

/-- More generally, output positions advance in lockstep with invocations
starting `D` cycles after a marker. -/
theorem outputPhase_after_delay (delay : Nat) (positive : 0 < delay)
    (offset : Nat) :
    outputPhase delay positive
        (phaseOfNat delay positive (delay + offset)) =
      phaseOfNat delay positive offset := by
  apply Fin.ext
  simp only [outputPhase, phaseOfNat, Fin.val_mk]
  rw [Nat.mod_add_mod]
  rw [show delay + offset + delay = offset + 2 * delay by omega]
  simp

/-! ## Frame-relative schedule

The following definitions describe the intended commutator result without any
state.  A complete frame consists of `groups` periods, each of length
`2 * delay`.  The phase selects which physical input half is active; the two
input cycles are always `delay` positions apart within the same group.
-/

/-- Split a frame-relative output cycle into its group and local phase. -/
def frameCoordinate (groups delay : Nat) :
    Fin (groups * (2 * delay)) ≃ Fin groups × Fin (2 * delay) :=
  finProdFinEquiv.symm

/-- The two input cycles paired at one frame-relative output cycle. -/
def pairedInputCycles (groups delay : Nat) (_positive : 0 < delay)
    (outputCycle : Fin (groups * (2 * delay))) :
    Fin (groups * (2 * delay)) × Fin (groups * (2 * delay)) :=
  let coordinate := frameCoordinate groups delay outputCycle
  if firstHalf : coordinate.2.val < delay then
    (finProdFinEquiv (coordinate.1,
      ⟨coordinate.2.val, coordinate.2.isLt⟩),
     finProdFinEquiv (coordinate.1,
      ⟨coordinate.2.val + delay, by omega⟩))
  else
    (finProdFinEquiv (coordinate.1,
      ⟨coordinate.2.val - delay, by omega⟩),
     finProdFinEquiv (coordinate.1,
      ⟨coordinate.2.val, coordinate.2.isLt⟩))

/-- Stateless operand pair required at one frame-relative output cycle. -/
def scheduledOperands (groups delay : Nat) (positive : 0 < delay)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (outputCycle : Fin (groups * (2 * delay))) : Operands α :=
  let coordinate := frameCoordinate groups delay outputCycle
  let inputCycles := pairedInputCycles groups delay positive outputCycle
  if coordinate.2.val < delay then
    { a := (frame inputCycles.1).a
      b := (frame inputCycles.2).a }
  else
    { a := (frame inputCycles.1).b
      b := (frame inputCycles.2).b }

/-- The frame-relative output-period position associated with one scheduled
operand pair.  This control value must be delayed alongside the data rather
than reconstructed from a possibly rephased later input cycle. -/
def scheduledPhase (groups delay : Nat)
    (outputCycle : Fin (groups * (2 * delay))) : Fin (2 * delay) :=
  (frameCoordinate groups delay outputCycle).2

/-- Input cycles needed to observe one complete output frame: the complete
marked frame followed by an arbitrary `delay`-cycle continuation.  Values in
the continuation may belong to a later frame; the schedule theorem proves
that they cannot change the earlier frame's result. -/
def frameExecutionInputs (groups delay : Nat)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α) : List (Input α) :=
  List.ofFn frame ++ List.ofFn continuation

/-- Execute one complete frame far enough to expose all of its delayed
operand pairs. -/
def runFrame (groups delay : Nat) (positive : 0 < delay)
    (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α) :
    List (Signals delay α) × State delay α :=
  runDetailed delay positive state
    (frameExecutionInputs groups delay frame continuation)

/-- The detailed signals at a selected input position. -/
def visibleAt (delay : Nat) (positive : 0 < delay)
    (state : State delay α) (inputs : List (Input α))
    (position : Nat) (occurs : position < inputs.length) : Signals delay α :=
  (runDetailed delay positive state inputs).1.get
    ⟨position, by
      rw [runDetailed_length]
      exact occurs⟩

/-- Detailed commutator signals carrying one selected frame-relative output
cycle. -/
def frameSignal (groups delay : Nat) (positive : 0 < delay)
    (state : State delay α)
    (frame : Fin (groups * (2 * delay)) → Input α)
    (continuation : Fin delay → Input α)
    (outputCycle : Fin (groups * (2 * delay))) : Signals delay α :=
  visibleAt delay positive state
    (frameExecutionInputs groups delay frame continuation)
    (delay + outputCycle.val) (by
      simp [frameExecutionInputs]
      omega)

end Commutator

/-! ## Parallel commutator bank

All butterflies in a streamed stage share the same phase and frame marker, but
their two data paths have independent contents.  The pure bank is therefore a
pointwise family of the proved single-lane commutator.  This is the reusable
correspondence target for the later structural splitter, shift-register, and
butterfly bank.
-/

namespace CommutatorBank

/-- One synchronized input cycle for a parallel commutator bank. -/
structure Input (lanes : Nat) (α : Type u) where
  first : Bool
  a : Fin lanes → α
  b : Fin lanes → α

/-- Independent delay contents for every physical butterfly lane. -/
abbrev State (lanes delay : Nat) (α : Type u) :=
  Fin lanes → Commutator.State delay α

/-- Project one bank input onto the ordinary single-lane commutator input. -/
def laneInput {lanes : Nat} (input : Input lanes α) (lane : Fin lanes) :
    Commutator.Input α :=
  { first := input.first, a := input.a lane, b := input.b lane }

/-- Execute all commutator lanes over the same synchronized frame. -/
def runFrame (lanes groups delay : Nat) (positive : 0 < delay)
    (state : State lanes delay α)
    (frame : Fin (groups * (2 * delay)) → Input lanes α)
    (continuation : Fin delay → Input lanes α) :
    Fin lanes → List (Commutator.Signals delay α) × Commutator.State delay α :=
  fun lane => Commutator.runFrame groups delay positive (state lane)
    (fun cycle => laneInput (frame cycle) lane)
    (fun cycle => laneInput (continuation cycle) lane)

/-- Signals belonging to one bank lane and one frame-relative output cycle. -/
def frameSignal (groups delay : Nat) (positive : 0 < delay)
    (state : State lanes delay α)
    (frame : Fin (groups * (2 * delay)) → Input lanes α)
    (continuation : Fin delay → Input lanes α)
    (cycle : Fin (groups * (2 * delay))) (lane : Fin lanes) :
    Commutator.Signals delay α :=
  Commutator.frameSignal groups delay positive (state lane)
    (fun inputCycle => laneInput (frame inputCycle) lane)
    (fun continuationCycle => laneInput (continuation continuationCycle) lane)
    cycle

/-- `frameSignal` is the selected entry of the executable bank trace.  This
keeps pointwise scheduling theorems connected to the generic `runFrame`
model used by executable checks and, later, by the structural refinement. -/
theorem frameSignal_eq_runFrame_get (groups delay : Nat) (positive : 0 < delay)
    (state : State lanes delay α)
    (frame : Fin (groups * (2 * delay)) → Input lanes α)
    (continuation : Fin delay → Input lanes α)
    (cycle : Fin (groups * (2 * delay))) (lane : Fin lanes) :
    frameSignal groups delay positive state frame continuation cycle lane =
      (runFrame lanes groups delay positive state frame continuation lane).1.get
        ⟨delay + cycle.val, by
          simp [runFrame, Commutator.runFrame,
            Commutator.frameExecutionInputs, Commutator.runDetailed_length]
          omega⟩ := by
  rfl

end CommutatorBank

/-- The stage's pair delay is always positive. -/
@[simp] theorem Geometry.pairDelay_pos (geometry : Geometry depth) :
    0 < geometry.pairDelay := by
  simp [Geometry.pairDelay]

/-- Number of parallel butterflies in a streamed stage. -/
def butterflyCount (geometry : Geometry depth) : Nat :=
  geometry.inputBoundary.lanesPerBranch

@[simp] theorem butterflyCount_pos (geometry : Geometry depth) :
    0 < butterflyCount geometry := by
  simp [butterflyCount, BoundaryGeometry.lanesPerBranch]

/-- The local control period is exactly the commutator phase cardinality. -/
theorem Geometry.localPeriod_eq_commutatorPeriod (geometry : Geometry depth) :
    geometry.localPeriod = 2 * geometry.pairDelay :=
  geometry.localPeriod_eq_two_mul_pairDelay

/-- Reinterpret a physical frame cycle as a commutator group and local
`2 * pairDelay` phase.  The equivalence preserves the underlying linear cycle
number. -/
def Geometry.scheduleCycleEquiv (geometry : Geometry depth) :
    Fin geometry.frameLength ≃
      Fin (geometry.outputBoundary.groupCount * (2 * geometry.pairDelay)) :=
  finCongr (by
    calc
      geometry.frameLength =
          geometry.outputBoundary.groupCount * geometry.localPeriod :=
        geometry.output_groupCount_mul_localPeriod.symm
      _ = geometry.outputBoundary.groupCount * (2 * geometry.pairDelay) := by
        rw [Geometry.localPeriod_eq_commutatorPeriod geometry])

@[simp] theorem Geometry.scheduleCycleEquiv_val (geometry : Geometry depth)
    (cycle : Fin geometry.frameLength) :
    (Geometry.scheduleCycleEquiv geometry cycle).val = cycle.val := by
  rfl

@[simp] theorem Geometry.scheduleCycleEquiv_symm_val (geometry : Geometry depth)
    (cycle : Fin
      (geometry.outputBoundary.groupCount * (2 * geometry.pairDelay))) :
    ((Geometry.scheduleCycleEquiv geometry).symm cycle).val = cycle.val := by
  rfl

/-- Low physical lane identifying one butterfly in the parallel bank. -/
def bankLane (geometry : Geometry depth) (lane : Fin geometry.laneCount) :
    Fin (butterflyCount geometry) :=
  (geometry.outputBoundary.laneEquiv lane).2

/-- Physical output lane carrying one selected butterfly branch. -/
def outputLane (geometry : Geometry depth) (branch : Fin 2)
    (lane : Fin (butterflyCount geometry)) : Fin geometry.laneCount :=
  geometry.outputBoundary.laneEquiv.symm (branch, lane)

/-- The streamed output groups are exactly the ordinary butterfly-layer
groups at this stage. -/
theorem outputGroupCount_eq_layerGroupCount (geometry : Geometry depth) :
    geometry.outputBoundary.groupCount =
      2 ^ (depth - geometry.stage.val - 1) := by
  unfold BoundaryGeometry.groupCount Geometry.outputBoundary
  rw [Nat.sub_sub]

/-- The output-boundary offset is exactly the twiddle/within-branch offset of
the ordinary butterfly layer. -/
theorem outputOffsetsPerBranch_eq_layerOffsets (geometry : Geometry depth) :
    geometry.outputBoundary.offsetsPerBranch = 2 ^ geometry.stage.val := by
  unfold BoundaryGeometry.offsetsPerBranch Geometry.outputBoundary
  congr 2

/-- Logical butterfly position named directly by the physical output
group/period/lane coordinates. -/
def scheduledPosition (geometry : Geometry depth)
    (cycle : Fin geometry.frameLength) (branch : Fin 2)
    (lane : Fin (butterflyCount geometry)) :
    HTFFT.Exact.LayerPosition depth geometry.stage :=
  { group := Fin.cast (outputGroupCount_eq_layerGroupCount geometry)
      (geometry.outputBoundary.cycleEquiv cycle).1
    branch := branch
    offset := Fin.cast (outputOffsetsPerBranch_eq_layerOffsets geometry)
      (geometry.outputBoundary.offsetEquiv
        ((geometry.outputBoundary.cycleEquiv cycle).2, lane)) }

/-- Twiddle ROM address formed from one delayed output-period phase and the
low parallel-bank lane. -/
def twiddleAddress (geometry : Geometry depth)
    (phase : Fin (2 * geometry.pairDelay))
    (lane : Fin (butterflyCount geometry)) : Fin (2 ^ geometry.stage.val) :=
  let outputBatch := Fin.cast
    (Geometry.localPeriod_eq_commutatorPeriod geometry).symm phase
  Fin.cast (outputOffsetsPerBranch_eq_layerOffsets geometry)
    (geometry.outputBoundary.offsetEquiv (outputBatch, lane))

/-- Stateless twiddle address associated with one physical output cycle. -/
def scheduledTwiddleAddress (geometry : Geometry depth)
    (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) : Fin (2 ^ geometry.stage.val) :=
  twiddleAddress geometry
    (Commutator.scheduledPhase geometry.outputBoundary.groupCount
      geometry.pairDelay (Geometry.scheduleCycleEquiv geometry cycle)) lane

/-- Physical input coordinate selected for one logical branch of the
butterfly produced at `cycle` on `lane`. -/
def scheduledInputCoordinate (geometry : Geometry depth)
    (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) (branch : Fin 2) :
    Fin geometry.frameLength × Fin geometry.laneCount :=
  let scheduleCycle := Geometry.scheduleCycleEquiv geometry cycle
  let pair := Commutator.pairedInputCycles
    geometry.outputBoundary.groupCount geometry.pairDelay
    (Geometry.pairDelay_pos geometry) scheduleCycle
  let inputCycle := if branch = 0 then pair.1 else pair.2
  let phase := Commutator.scheduledPhase geometry.outputBoundary.groupCount
    geometry.pairDelay scheduleCycle
  let inputLaneBranch : Fin 2 := if phase.val < geometry.pairDelay then 0 else 1
  ((Geometry.scheduleCycleEquiv geometry).symm inputCycle,
    geometry.inputBoundary.laneEquiv.symm (inputLaneBranch, lane))

/-- Split an output-period position into the input-lane branch bit and the
input-boundary batch position. -/
def outputPhaseEquiv (geometry : Geometry depth) :
    Fin geometry.localPeriod ≃ Fin 2 × Fin geometry.pairDelay :=
  (finCongr (Geometry.localPeriod_eq_commutatorPeriod geometry)).trans
    finProdFinEquiv.symm

/-- Input-boundary group containing one logical branch of an output group. -/
def inputGroup (geometry : Geometry depth)
    (group : Fin geometry.outputBoundary.groupCount) (branch : Fin 2) :
    Fin geometry.inputBoundary.groupCount :=
  Fin.cast (by
    calc
      geometry.outputBoundary.groupCount * 2 =
          2 * geometry.outputBoundary.groupCount := Nat.mul_comm _ _
      _ = geometry.inputBoundary.groupCount :=
        geometry.input_groupCount_eq_two_mul_output_groupCount.symm)
    (finProdFinEquiv (group, branch))

/-- The same logical input coordinate expressed directly in the input
boundary's group/batch/lane decomposition. -/
def layoutInputCoordinate (geometry : Geometry depth)
    (cycle : Fin geometry.frameLength)
    (lane : Fin (butterflyCount geometry)) (branch : Fin 2) :
    Fin geometry.frameLength × Fin geometry.laneCount :=
  let outputCycle := geometry.outputBoundary.cycleEquiv cycle
  let phase := outputPhaseEquiv geometry outputCycle.2
  (geometry.inputBoundary.cycleEquiv.symm
      (inputGroup geometry outputCycle.1 branch, phase.2),
    geometry.inputBoundary.laneEquiv.symm (phase.1, lane))

/-- Split one physical input payload into the two lane halves consumed by the
parallel commutator bank. -/
def bankInput (geometry : Geometry depth) (first : Bool)
    (data : Fin geometry.laneCount → α) :
    CommutatorBank.Input (butterflyCount geometry) α :=
  { first := first
    a := fun lane =>
      data (geometry.inputBoundary.laneEquiv.symm (0, lane))
    b := fun lane =>
      data (geometry.inputBoundary.laneEquiv.symm (1, lane)) }

/-- Reindex a physical stage frame into the generic commutator-bank frame
shape while splitting every payload into its two lane halves. -/
def bankFrame (geometry : Geometry depth)
    (first : Fin geometry.frameLength → Bool)
    (data : Fin geometry.frameLength → Fin geometry.laneCount → α) :
    Fin (geometry.outputBoundary.groupCount * (2 * geometry.pairDelay)) →
      CommutatorBank.Input (butterflyCount geometry) α :=
  fun cycle =>
    let physicalCycle := (Geometry.scheduleCycleEquiv geometry).symm cycle
    bankInput geometry (first physicalCycle) (data physicalCycle)

/-! ## Logical meaning of one scheduled butterfly

The commutator moves one bit between the cycle and lane coordinates.  The
following definitions recover the corresponding ordinary layer position from
an output coordinate and then identify the two physical input coordinates
owned by that butterfly.  They are deliberately stated through the proved
boundary equivalences, keeping the schedule theorem independent of arithmetic
encodings of those coordinates.
-/

/-- Ordinary layer position produced at one physical output coordinate. -/
def outputPosition (geometry : Geometry depth)
    (cycle : Fin geometry.frameLength) (lane : Fin geometry.laneCount) :
    HTFFT.Exact.LayerPosition depth geometry.stage :=
  (HTFFT.Exact.layerIndexEquiv depth geometry.stage).symm
    (geometry.outputBoundary.layout (cycle, lane))

/-- Physical input coordinate supplying one branch of the butterfly that owns
the selected output coordinate. -/
def inputCoordinate (geometry : Geometry depth)
    (cycle : Fin geometry.frameLength) (lane : Fin geometry.laneCount)
    (branch : Fin 2) : Fin geometry.frameLength × Fin geometry.laneCount :=
  geometry.inputBoundary.layout.symm
    (HTFFT.Exact.layerIndexEquiv depth geometry.stage
      { outputPosition geometry cycle lane with branch := branch })

@[simp] theorem inputBoundary_layout_inputCoordinate
    (geometry : Geometry depth)
    (cycle : Fin geometry.frameLength) (lane : Fin geometry.laneCount)
    (branch : Fin 2) :
    geometry.inputBoundary.layout
        (inputCoordinate geometry cycle lane branch) =
      HTFFT.Exact.layerIndexEquiv depth geometry.stage
        { outputPosition geometry cycle lane with branch := branch } := by
  simp [inputCoordinate]

@[simp] theorem layerIndexEquiv_outputPosition
    (geometry : Geometry depth)
    (cycle : Fin geometry.frameLength) (lane : Fin geometry.laneCount) :
    HTFFT.Exact.layerIndexEquiv depth geometry.stage
        (outputPosition geometry cycle lane) =
      geometry.outputBoundary.layout (cycle, lane) := by
  simp [outputPosition]

/-- Pure scheduled stage result, expressed directly as one butterfly per
physical output coordinate.  The later structural proof only has to show that
the two-delay commutator presents these operands and twiddle at the advertised
cycle. -/
def scheduledOutputFrame (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (input : InputFrame configuration geometry) :
    OutputFrame configuration geometry :=
  fun cycle lane =>
    let position := outputPosition geometry cycle lane
    let firstCoordinate := inputCoordinate geometry cycle lane 0
    let secondCoordinate := inputCoordinate geometry cycle lane 1
    let dataFormat := configuration.boundaryFormat geometry.stage.castSucc
    let outputFormat := configuration.boundaryFormat geometry.stage.succ
    let first := PipelinedFixedButterfly.decodeComplex dataFormat.width
      (input firstCoordinate.1 firstCoordinate.2)
    let second := PipelinedFixedButterfly.decodeComplex dataFormat.width
      (input secondCoordinate.1 secondCoordinate.2)
    let result := HTFFT.Butterfly.Fixed.butterfly
      (configuration.fixedConfig.butterfly geometry.stage)
      first second (table.value geometry.stage position.offset)
    PipelinedFixedButterfly.encodeComplex outputFormat.width
      (if position.branch = 0 then result.upper else result.lower)

/-- Complete operand/control observations from the pure parallel commutator
bank, indexed in physical output-frame coordinates. -/
abbrev BankSignals (configuration : FFTConfiguration depth)
    (geometry : Geometry depth) :=
  Fin geometry.frameLength → Fin (butterflyCount geometry) →
    Commutator.Signals geometry.pairDelay
      ((complexSignalType
        (configuration.boundaryFormat geometry.stage.castSucc)).Denote)

/-- Physical-frame view of one pure parallel-bank execution. -/
def bankFrameSignals (configuration : FFTConfiguration depth)
    (geometry : Geometry depth)
    (state : CommutatorBank.State (butterflyCount geometry)
      geometry.pairDelay
      ((complexSignalType
        (configuration.boundaryFormat geometry.stage.castSucc)).Denote))
    (first : Fin geometry.frameLength → Bool)
    (input : InputFrame configuration geometry)
    (continuation : Fin geometry.pairDelay →
      CommutatorBank.Input (butterflyCount geometry)
        ((complexSignalType
          (configuration.boundaryFormat geometry.stage.castSucc)).Denote)) :
    BankSignals configuration geometry :=
  fun cycle lane =>
    CommutatorBank.frameSignal geometry.outputBoundary.groupCount
      geometry.pairDelay (Geometry.pairDelay_pos geometry) state
      (bankFrame geometry first input) continuation
      (Geometry.scheduleCycleEquiv geometry cycle) lane

/-- Evaluate the butterfly bank and twiddle table from pure commutator
observations.  This remains a functional model; it is the semantic target for
the later ROM and pipelined-butterfly structures. -/
def outputFrameOfBankSignals (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (signals : BankSignals configuration geometry) :
    OutputFrame configuration geometry :=
  fun cycle outputLaneIndex =>
    let laneCoordinate := geometry.outputBoundary.laneEquiv outputLaneIndex
    let visible := signals cycle laneCoordinate.2
    let dataFormat := configuration.boundaryFormat geometry.stage.castSucc
    let outputFormat := configuration.boundaryFormat geometry.stage.succ
    let first := PipelinedFixedButterfly.decodeComplex dataFormat.width
      visible.operands.a
    let second := PipelinedFixedButterfly.decodeComplex dataFormat.width
      visible.operands.b
    let result := HTFFT.Butterfly.Fixed.butterfly
      (configuration.fixedConfig.butterfly geometry.stage)
      first second
      (table.value geometry.stage
        (twiddleAddress geometry visible.outputPhase laneCoordinate.2))
    PipelinedFixedButterfly.encodeComplex outputFormat.width
      (if laneCoordinate.1 = 0 then result.upper else result.lower)

/-- The pure physical schedule is exactly the already approved natural layer
result.  This is the schedule's semantic obligation before any structural
wiring is introduced. -/
theorem scheduledOutputFrame_eq_contractResult
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (input : InputFrame configuration geometry) :
    scheduledOutputFrame configuration table geometry input =
      encodeOutputFrame configuration geometry
        (resultValue configuration table geometry input) := by
  funext cycle lane
  rfl

end HTFFT.Silean.FFTStage.Internal
