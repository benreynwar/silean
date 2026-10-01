import HTFFT.Silean.FinalReorder.FinalReorder

/-! Pure coordinate schedule for the final streamed reorder. -/

namespace HTFFT.Silean.FinalReorder.Internal
open FFT

/-- Number of samples in either half of one packed cycle. -/
abbrev halfLaneCount (configuration : Configuration depth) : Nat :=
  2 ^ (configuration.laneDepth - 1)

/-- Number of cycles in either half of one complete frame. -/
abbrev halfFrameLength (configuration : Configuration depth) : Nat :=
  configuration.finalReorderLatency

theorem two_mul_halfLaneCount (configuration : Configuration depth) :
    2 * halfLaneCount configuration = configuration.laneCount := by
  unfold halfLaneCount Configuration.laneCount
  have exponent : configuration.laneDepth - 1 + 1 =
      configuration.laneDepth := by
    have positive := configuration.laneDepth_pos
    omega
  calc
    2 * 2 ^ (configuration.laneDepth - 1) =
        2 ^ (configuration.laneDepth - 1) * 2 := by omega
    _ = 2 ^ (configuration.laneDepth - 1 + 1) := by rw [Nat.pow_succ]
    _ = 2 ^ configuration.laneDepth := by rw [exponent]

theorem two_mul_halfFrameLength (configuration : Configuration depth) :
    2 * halfFrameLength configuration = configuration.frameLength := by
  unfold halfFrameLength Configuration.frameLength
  unfold Configuration.finalReorderLatency
  have remainingPositive : 0 < depth - configuration.laneDepth := by
    have geometry := configuration.initialReorderGeometry
    have lanePositive := configuration.laneDepth_pos
    omega
  have exponent : depth - configuration.laneDepth - 1 + 1 =
      depth - configuration.laneDepth := by omega
  calc
    2 * 2 ^ (depth - configuration.laneDepth - 1) =
        2 ^ (depth - configuration.laneDepth - 1) * 2 := by omega
    _ = 2 ^ (depth - configuration.laneDepth - 1 + 1) := by
      rw [Nat.pow_succ]
    _ = 2 ^ (depth - configuration.laneDepth) := by rw [exponent]

theorem halfLaneCount_pos (configuration : Configuration depth) :
    0 < halfLaneCount configuration := by
  simp [halfLaneCount]

theorem halfFrameLength_pos (configuration : Configuration depth) :
    0 < halfFrameLength configuration := by
  exact configuration.finalReorderLatency_pos

/-- One lane-half across one frame-half contains exactly one logical half of
the complete transform vector. -/
theorem laneCount_mul_halfFrameLength (configuration : Configuration depth) :
    configuration.laneCount * halfFrameLength configuration =
      2 ^ (depth - 1) := by
  unfold Configuration.laneCount halfFrameLength
    Configuration.finalReorderLatency
  rw [← Nat.pow_add]
  congr 1
  have geometry := configuration.initialReorderGeometry
  have positive := configuration.laneDepth_pos
  omega

/-- A cycle in the first half of a frame. -/
def firstOutputCycle (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    Fin configuration.frameLength :=
  ⟨cycle.val, by
    have halfPositive := halfFrameLength_pos configuration
    have full := two_mul_halfFrameLength configuration
    omega⟩

/-- The corresponding cycle in the second half of a frame. -/
def secondOutputCycle (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    Fin configuration.frameLength :=
  ⟨halfFrameLength configuration + cycle.val, by
    have full := two_mul_halfFrameLength configuration
    omega⟩

/-- The even input cycle supplying the lower output half-vector. -/
def evenInputCycle (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    Fin configuration.frameLength :=
  ⟨2 * cycle.val, by
    have full := two_mul_halfFrameLength configuration
    omega⟩

/-- The odd input cycle supplying the upper output half-vector. -/
def oddInputCycle (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    Fin configuration.frameLength :=
  ⟨2 * cycle.val + 1, by
    have full := two_mul_halfFrameLength configuration
    omega⟩

/-- A lane in the lower half of one packed cycle. -/
def lowerLane (configuration : Configuration depth)
    (lane : Fin (halfLaneCount configuration)) :
    Fin configuration.laneCount :=
  ⟨lane.val, by
    have full := two_mul_halfLaneCount configuration
    have halfPositive := halfLaneCount_pos configuration
    omega⟩

/-- The corresponding lane in the upper half of one packed cycle. -/
def upperLane (configuration : Configuration depth)
    (lane : Fin (halfLaneCount configuration)) :
    Fin configuration.laneCount :=
  ⟨halfLaneCount configuration + lane.val, by
    have full := two_mul_halfLaneCount configuration
    omega⟩

@[simp] theorem firstOutputCycle_val (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    (firstOutputCycle configuration cycle).val = cycle.val := rfl

@[simp] theorem secondOutputCycle_val (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    (secondOutputCycle configuration cycle).val =
      halfFrameLength configuration + cycle.val := rfl

@[simp] theorem evenInputCycle_val (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    (evenInputCycle configuration cycle).val = 2 * cycle.val := rfl

@[simp] theorem oddInputCycle_val (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    (oddInputCycle configuration cycle).val = 2 * cycle.val + 1 := rfl

@[simp] theorem lowerLane_val (configuration : Configuration depth)
    (lane : Fin (halfLaneCount configuration)) :
    (lowerLane configuration lane).val = lane.val := rfl

@[simp] theorem upperLane_val (configuration : Configuration depth)
    (lane : Fin (halfLaneCount configuration)) :
    (upperLane configuration lane).val =
      halfLaneCount configuration + lane.val := rfl

private theorem resultFrame_eq_of_layout
    (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (source output : Fin configuration.frameLength ×
      Fin configuration.laneCount)
    (coordinate : configuration.finalGeometry.layout source =
      naturalLayout configuration output) :
    resultFrame configuration input output.1 output.2 =
      input source.1 source.2 := by
  unfold resultFrame packOutput unpackFinalPhysical
    FFTStage.BoundaryGeometry.unpack
  rw [← coordinate, Equiv.symm_apply_apply]

/-- The final physical layout associates each first-half output cycle with two
consecutive lower-branch input half-vectors. -/
theorem first_lower
    (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin (halfFrameLength configuration))
    (lane : Fin (halfLaneCount configuration)) :
    resultFrame configuration input
        (firstOutputCycle configuration cycle)
        (lowerLane configuration lane) =
      input (evenInputCycle configuration cycle)
        (lowerLane configuration lane) := by
  have coordinate :
      configuration.finalGeometry.layout
          (evenInputCycle configuration cycle,
            lowerLane configuration lane) =
        naturalLayout configuration
          (firstOutputCycle configuration cycle,
            lowerLane configuration lane) := by
    apply Fin.ext
    rw [FFTStage.BoundaryGeometry.layout_val]
    rw [FFTStage.BoundaryGeometry.laneEquiv_snd_val,
      FFTStage.BoundaryGeometry.cycleEquiv_snd_val,
      FFTStage.BoundaryGeometry.laneEquiv_fst_val,
      FFTStage.BoundaryGeometry.cycleEquiv_fst_val]
    simp only [Configuration.finalGeometry,
      FFTStage.BoundaryGeometry.batchCount,
      FFTStage.BoundaryGeometry.lanesPerBranch,
      FFTStage.BoundaryGeometry.offsetsPerBranch,
      evenInputCycle_val, lowerLane_val, naturalLayout_val,
      firstOutputCycle_val, Fin.val_last]
    have laneBound : lane.val < 2 ^ (configuration.laneDepth - 1) :=
      lane.isLt
    have cycleBound : 2 * cycle.val <
        2 ^ (depth - configuration.laneDepth) := by
      change 2 * cycle.val < configuration.frameLength
      rw [← two_mul_halfFrameLength configuration]
      omega
    rw [Nat.mod_eq_of_lt laneBound, Nat.div_eq_of_lt laneBound,
      Nat.mod_eq_of_lt cycleBound, Nat.div_eq_of_lt cycleBound]
    simp only [Nat.mul_zero, Nat.add_zero]
    calc
      lane.val + 2 ^ (configuration.laneDepth - 1) * (2 * cycle.val) =
          lane.val + (2 * halfLaneCount configuration) * cycle.val := by
        unfold halfLaneCount
        ring
      _ = lane.val + configuration.laneCount * cycle.val := by
        rw [two_mul_halfLaneCount]
  exact resultFrame_eq_of_layout configuration input
    (evenInputCycle configuration cycle, lowerLane configuration lane)
    (firstOutputCycle configuration cycle, lowerLane configuration lane)
    coordinate

theorem first_upper
    (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin (halfFrameLength configuration))
    (lane : Fin (halfLaneCount configuration)) :
    resultFrame configuration input
        (firstOutputCycle configuration cycle)
        (upperLane configuration lane) =
      input (oddInputCycle configuration cycle)
        (lowerLane configuration lane) := by
  apply resultFrame_eq_of_layout configuration input
    (oddInputCycle configuration cycle, lowerLane configuration lane)
    (firstOutputCycle configuration cycle, upperLane configuration lane)
  apply Fin.ext
  rw [FFTStage.BoundaryGeometry.layout_val]
  rw [FFTStage.BoundaryGeometry.laneEquiv_snd_val,
    FFTStage.BoundaryGeometry.cycleEquiv_snd_val,
    FFTStage.BoundaryGeometry.laneEquiv_fst_val,
    FFTStage.BoundaryGeometry.cycleEquiv_fst_val]
  simp only [Configuration.finalGeometry,
    FFTStage.BoundaryGeometry.batchCount,
    FFTStage.BoundaryGeometry.lanesPerBranch,
    FFTStage.BoundaryGeometry.offsetsPerBranch,
    oddInputCycle_val, lowerLane_val, upperLane_val, naturalLayout_val,
    firstOutputCycle_val, Fin.val_last]
  have laneBound : lane.val < 2 ^ (configuration.laneDepth - 1) :=
    lane.isLt
  have cycleBound : 2 * cycle.val + 1 <
      2 ^ (depth - configuration.laneDepth) := by
    change 2 * cycle.val + 1 < configuration.frameLength
    rw [← two_mul_halfFrameLength configuration]
    omega
  rw [Nat.mod_eq_of_lt laneBound, Nat.div_eq_of_lt laneBound,
    Nat.mod_eq_of_lt cycleBound, Nat.div_eq_of_lt cycleBound]
  simp only [Nat.mul_zero, Nat.add_zero]
  calc
    lane.val + 2 ^ (configuration.laneDepth - 1) *
        (2 * cycle.val + 1) =
      halfLaneCount configuration + lane.val +
        (2 * halfLaneCount configuration) * cycle.val := by
      unfold halfLaneCount
      ring
    _ = halfLaneCount configuration + lane.val +
        configuration.laneCount * cycle.val := by
      rw [two_mul_halfLaneCount]

/-- The second output half consumes the same even/odd cycle pairing from the
upper branch of the final physical layout. -/
theorem second_lower
    (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin (halfFrameLength configuration))
    (lane : Fin (halfLaneCount configuration)) :
    resultFrame configuration input
        (secondOutputCycle configuration cycle)
        (lowerLane configuration lane) =
      input (evenInputCycle configuration cycle)
        (upperLane configuration lane) := by
  apply resultFrame_eq_of_layout configuration input
    (evenInputCycle configuration cycle, upperLane configuration lane)
    (secondOutputCycle configuration cycle, lowerLane configuration lane)
  apply Fin.ext
  rw [FFTStage.BoundaryGeometry.layout_val]
  rw [FFTStage.BoundaryGeometry.laneEquiv_snd_val,
    FFTStage.BoundaryGeometry.cycleEquiv_snd_val,
    FFTStage.BoundaryGeometry.laneEquiv_fst_val,
    FFTStage.BoundaryGeometry.cycleEquiv_fst_val]
  simp only [Configuration.finalGeometry,
    FFTStage.BoundaryGeometry.batchCount,
    FFTStage.BoundaryGeometry.lanesPerBranch,
    FFTStage.BoundaryGeometry.offsetsPerBranch,
    evenInputCycle_val, lowerLane_val, upperLane_val, naturalLayout_val,
    secondOutputCycle_val, Fin.val_last]
  have laneBound : lane.val < 2 ^ (configuration.laneDepth - 1) :=
    lane.isLt
  have laneHalfPositive : 0 < 2 ^ (configuration.laneDepth - 1) :=
    Nat.two_pow_pos _
  have cycleBound : 2 * cycle.val <
      2 ^ (depth - configuration.laneDepth) := by
    change 2 * cycle.val < configuration.frameLength
    rw [← two_mul_halfFrameLength configuration]
    omega
  have upperMod :
      (2 ^ (configuration.laneDepth - 1) + lane.val) %
          2 ^ (configuration.laneDepth - 1) = lane.val := by
    rw [Nat.add_mod]
    simp only [Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt laneBound]
  have upperDiv :
      (2 ^ (configuration.laneDepth - 1) + lane.val) /
          2 ^ (configuration.laneDepth - 1) = 1 := by
    rw [Nat.add_div_left lane.val laneHalfPositive,
      Nat.div_eq_of_lt laneBound]
  rw [upperMod, upperDiv]
  rw [Nat.mod_eq_of_lt cycleBound, Nat.div_eq_of_lt cycleBound]
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero]
  rw [← laneCount_mul_halfFrameLength configuration]
  calc
    lane.val + 2 ^ (configuration.laneDepth - 1) * (2 * cycle.val) +
        configuration.laneCount * halfFrameLength configuration =
      lane.val + configuration.laneCount *
        (halfFrameLength configuration + cycle.val) := by
      rw [← two_mul_halfLaneCount configuration]
      unfold halfLaneCount
      ring

theorem second_upper
    (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin (halfFrameLength configuration))
    (lane : Fin (halfLaneCount configuration)) :
    resultFrame configuration input
        (secondOutputCycle configuration cycle)
        (upperLane configuration lane) =
      input (oddInputCycle configuration cycle)
        (upperLane configuration lane) := by
  apply resultFrame_eq_of_layout configuration input
    (oddInputCycle configuration cycle, upperLane configuration lane)
    (secondOutputCycle configuration cycle, upperLane configuration lane)
  apply Fin.ext
  rw [FFTStage.BoundaryGeometry.layout_val]
  rw [FFTStage.BoundaryGeometry.laneEquiv_snd_val,
    FFTStage.BoundaryGeometry.cycleEquiv_snd_val,
    FFTStage.BoundaryGeometry.laneEquiv_fst_val,
    FFTStage.BoundaryGeometry.cycleEquiv_fst_val]
  simp only [Configuration.finalGeometry,
    FFTStage.BoundaryGeometry.batchCount,
    FFTStage.BoundaryGeometry.lanesPerBranch,
    FFTStage.BoundaryGeometry.offsetsPerBranch,
    oddInputCycle_val, upperLane_val, naturalLayout_val,
    secondOutputCycle_val, Fin.val_last]
  have laneBound : lane.val < 2 ^ (configuration.laneDepth - 1) :=
    lane.isLt
  have laneHalfPositive : 0 < 2 ^ (configuration.laneDepth - 1) :=
    Nat.two_pow_pos _
  have cycleBound : 2 * cycle.val + 1 <
      2 ^ (depth - configuration.laneDepth) := by
    change 2 * cycle.val + 1 < configuration.frameLength
    rw [← two_mul_halfFrameLength configuration]
    omega
  have upperMod :
      (2 ^ (configuration.laneDepth - 1) + lane.val) %
          2 ^ (configuration.laneDepth - 1) = lane.val := by
    rw [Nat.add_mod]
    simp only [Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt laneBound]
  have upperDiv :
      (2 ^ (configuration.laneDepth - 1) + lane.val) /
          2 ^ (configuration.laneDepth - 1) = 1 := by
    rw [Nat.add_div_left lane.val laneHalfPositive,
      Nat.div_eq_of_lt laneBound]
  rw [upperMod, upperDiv]
  rw [Nat.mod_eq_of_lt cycleBound, Nat.div_eq_of_lt cycleBound]
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero]
  rw [← laneCount_mul_halfFrameLength configuration]
  calc
    lane.val + 2 ^ (configuration.laneDepth - 1) *
          (2 * cycle.val + 1) +
        configuration.laneCount * halfFrameLength configuration =
      halfLaneCount configuration + lane.val +
        configuration.laneCount *
          (halfFrameLength configuration + cycle.val) := by
      rw [← two_mul_halfLaneCount configuration]
      unfold halfLaneCount
      ring

private theorem cycle_div_two_lt_halfFrameLength
    (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    cycle.val / 2 < halfFrameLength configuration := by
  have full := two_mul_halfFrameLength configuration
  have bound := cycle.isLt
  omega

/-- Address used by the first half-vector bank for one input cycle. Even
cycles fill the lower address half with lower-lane chunks; odd cycles fill the
upper address half with upper-lane chunks. -/
def firstBankWriteAddress (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    Fin configuration.frameLength :=
  if even : cycle.val % 2 = 0 then
    ⟨cycle.val / 2, lt_of_lt_of_le
      (cycle_div_two_lt_halfFrameLength configuration cycle)
      (by
        have full := two_mul_halfFrameLength configuration
        have positive := halfFrameLength_pos configuration
        omega)⟩
  else
    ⟨halfFrameLength configuration + cycle.val / 2, by
      have halfBound := cycle_div_two_lt_halfFrameLength configuration cycle
      have full := two_mul_halfFrameLength configuration
      omega⟩

/-- The second bank uses the complementary address half. -/
def secondBankWriteAddress (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    Fin configuration.frameLength :=
  if even : cycle.val % 2 = 0 then
    ⟨halfFrameLength configuration + cycle.val / 2, by
      have halfBound := cycle_div_two_lt_halfFrameLength configuration cycle
      have full := two_mul_halfFrameLength configuration
      omega⟩
  else
    ⟨cycle.val / 2, lt_of_lt_of_le
      (cycle_div_two_lt_halfFrameLength configuration cycle)
      (by
        have full := two_mul_halfFrameLength configuration
        have positive := halfFrameLength_pos configuration
        omega)⟩

theorem firstBankWriteAddress_injective
    (configuration : Configuration depth) :
    Function.Injective (firstBankWriteAddress configuration) := by
  intro left right equal
  apply Fin.ext
  have numeric := congrArg Fin.val equal
  have leftRemainder : left.val % 2 < 2 := Nat.mod_lt _ (by omega)
  have rightRemainder : right.val % 2 < 2 := Nat.mod_lt _ (by omega)
  have halfPositive := halfFrameLength_pos configuration
  by_cases leftEven : left.val % 2 = 0 <;>
    by_cases rightEven : right.val % 2 = 0
  · simp [firstBankWriteAddress, leftEven, rightEven] at numeric
    have leftIdentity := Nat.div_add_mod left.val 2
    have rightIdentity := Nat.div_add_mod right.val 2
    omega
  · have rightOdd : right.val % 2 = 1 := by omega
    simp [firstBankWriteAddress, leftEven, rightEven] at numeric
    have leftHalfBound := cycle_div_two_lt_halfFrameLength configuration left
    omega
  · have leftOdd : left.val % 2 = 1 := by omega
    simp [firstBankWriteAddress, leftEven, rightEven] at numeric
    have rightHalfBound := cycle_div_two_lt_halfFrameLength configuration right
    omega
  · have leftOdd : left.val % 2 = 1 := by omega
    have rightOdd : right.val % 2 = 1 := by omega
    simp [firstBankWriteAddress, leftEven, rightEven] at numeric
    have leftIdentity := Nat.div_add_mod left.val 2
    have rightIdentity := Nat.div_add_mod right.val 2
    omega

theorem secondBankWriteAddress_injective
    (configuration : Configuration depth) :
    Function.Injective (secondBankWriteAddress configuration) := by
  intro left right equal
  apply Fin.ext
  have numeric := congrArg Fin.val equal
  have leftRemainder : left.val % 2 < 2 := Nat.mod_lt _ (by omega)
  have rightRemainder : right.val % 2 < 2 := Nat.mod_lt _ (by omega)
  have halfPositive := halfFrameLength_pos configuration
  by_cases leftEven : left.val % 2 = 0 <;>
    by_cases rightEven : right.val % 2 = 0
  · simp [secondBankWriteAddress, leftEven, rightEven] at numeric
    have leftIdentity := Nat.div_add_mod left.val 2
    have rightIdentity := Nat.div_add_mod right.val 2
    omega
  · have rightOdd : right.val % 2 = 1 := by omega
    simp [secondBankWriteAddress, leftEven, rightEven] at numeric
    have rightHalfBound := cycle_div_two_lt_halfFrameLength configuration right
    omega
  · have leftOdd : left.val % 2 = 1 := by omega
    simp [secondBankWriteAddress, leftEven, rightEven] at numeric
    have leftHalfBound := cycle_div_two_lt_halfFrameLength configuration left
    omega
  · have leftOdd : left.val % 2 = 1 := by omega
    have rightOdd : right.val % 2 = 1 := by omega
    simp [secondBankWriteAddress, leftEven, rightEven] at numeric
    have leftIdentity := Nat.div_add_mod left.val 2
    have rightIdentity := Nat.div_add_mod right.val 2
    omega

def lowerChunk (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin configuration.frameLength) :
    Fin (halfLaneCount configuration) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.arithmetic.boundaryFormat (Fin.last depth))).Denote :=
  fun lane => input cycle (lowerLane configuration lane)

def upperChunk (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin configuration.frameLength) :
    Fin (halfLaneCount configuration) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.arithmetic.boundaryFormat (Fin.last depth))).Denote :=
  fun lane => input cycle (upperLane configuration lane)

/-- Chunk written to the first bank on one input cycle. -/
def firstBankWriteChunk (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin configuration.frameLength) :=
  if cycle.val % 2 = 0 then
    lowerChunk configuration input cycle
  else
    upperChunk configuration input cycle

/-- Chunk written to the second bank on one input cycle. -/
def secondBankWriteChunk (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin configuration.frameLength) :=
  if cycle.val % 2 = 0 then
    upperChunk configuration input cycle
  else
    lowerChunk configuration input cycle

@[simp] theorem firstBankWriteAddress_even
    (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    firstBankWriteAddress configuration
        (evenInputCycle configuration cycle) =
      firstOutputCycle configuration cycle := by
  apply Fin.ext
  simp [firstBankWriteAddress, evenInputCycle]

@[simp] theorem secondBankWriteAddress_even
    (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    secondBankWriteAddress configuration
        (evenInputCycle configuration cycle) =
      secondOutputCycle configuration cycle := by
  apply Fin.ext
  simp [secondBankWriteAddress, evenInputCycle]

@[simp] theorem firstBankWriteAddress_odd
    (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    firstBankWriteAddress configuration
        (oddInputCycle configuration cycle) =
      secondOutputCycle configuration cycle := by
  apply Fin.ext
  have quotient : (2 * cycle.val + 1) / 2 = cycle.val := by omega
  simp [firstBankWriteAddress, oddInputCycle, quotient]

@[simp] theorem secondBankWriteAddress_odd
    (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    secondBankWriteAddress configuration
        (oddInputCycle configuration cycle) =
      firstOutputCycle configuration cycle := by
  apply Fin.ext
  have quotient : (2 * cycle.val + 1) / 2 = cycle.val := by omega
  simp [secondBankWriteAddress, oddInputCycle, quotient]

@[simp] theorem firstBankWriteChunk_even
    (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin (halfFrameLength configuration)) :
    firstBankWriteChunk configuration input
        (evenInputCycle configuration cycle) =
      lowerChunk configuration input (evenInputCycle configuration cycle) := by
  simp [firstBankWriteChunk, evenInputCycle]

@[simp] theorem secondBankWriteChunk_even
    (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin (halfFrameLength configuration)) :
    secondBankWriteChunk configuration input
        (evenInputCycle configuration cycle) =
      upperChunk configuration input (evenInputCycle configuration cycle) := by
  simp [secondBankWriteChunk, evenInputCycle]

@[simp] theorem firstBankWriteChunk_odd
    (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin (halfFrameLength configuration)) :
    firstBankWriteChunk configuration input
        (oddInputCycle configuration cycle) =
      upperChunk configuration input (oddInputCycle configuration cycle) := by
  simp [firstBankWriteChunk, oddInputCycle]

@[simp] theorem secondBankWriteChunk_odd
    (configuration : Configuration depth)
    (input : OutputFrame configuration)
    (cycle : Fin (halfFrameLength configuration)) :
    secondBankWriteChunk configuration input
        (oddInputCycle configuration cycle) =
      lowerChunk configuration input (oddInputCycle configuration cycle) := by
  simp [secondBankWriteChunk, oddInputCycle]

/-- Every even lower-branch chunk is written before its first-half output
cycle. -/
theorem even_write_before_first_read
    (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    (evenInputCycle configuration cycle).val <
      halfFrameLength configuration +
        (firstOutputCycle configuration cycle).val := by
  simp only [evenInputCycle_val, firstOutputCycle_val]
  omega

/-- Odd lower-branch chunks are also written before their reads, except for
the final chunk, whose write and read coincide and therefore needs the VHDL
bypass path. -/
theorem odd_write_le_first_read
    (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    (oddInputCycle configuration cycle).val ≤
      halfFrameLength configuration +
        (firstOutputCycle configuration cycle).val := by
  simp only [oddInputCycle_val, firstOutputCycle_val]
  omega

theorem odd_write_eq_first_read_iff
    (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    (oddInputCycle configuration cycle).val =
        halfFrameLength configuration +
          (firstOutputCycle configuration cycle).val ↔
      cycle.val + 1 = halfFrameLength configuration := by
  simp only [oddInputCycle_val, firstOutputCycle_val]
  omega

/-- Both upper-branch chunks were written in the preceding frame before their
second-half output cycles, even while the next frame is being accepted. -/
theorem even_write_before_second_read
    (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    (evenInputCycle configuration cycle).val <
      halfFrameLength configuration +
        (secondOutputCycle configuration cycle).val := by
  simp only [evenInputCycle_val, secondOutputCycle_val]
  omega

theorem odd_write_before_second_read
    (configuration : Configuration depth)
    (cycle : Fin (halfFrameLength configuration)) :
    (oddInputCycle configuration cycle).val <
      halfFrameLength configuration +
        (secondOutputCycle configuration cycle).val := by
  simp only [oddInputCycle_val, secondOutputCycle_val]
  have positive := halfFrameLength_pos configuration
  omega

end HTFFT.Silean.FinalReorder.Internal
