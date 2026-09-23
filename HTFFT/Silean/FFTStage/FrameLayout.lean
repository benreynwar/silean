import HTFFT.Exact.Layered
import Silean.Semantics.FramedLatency

namespace HTFFT.Silean.FFTStage

/-! # Streaming FFT frame layouts

A complete depth-`depth` FFT vector is carried over `2^(depth-laneDepth)`
cycles, with `2^laneDepth` samples per cycle.  The efficient streaming
architecture does not keep a fixed cycle-major layout between rolled layers.
Each completed layer moves its branch bit into the most-significant physical
lane bit and moves the previous lane bit into the cycle coordinate.

`BoundaryGeometry.layout` states that permutation independently of delay
registers, counters, and butterfly wiring.  It is the shared meaning of a
streamed frame at one boundary of the layered FFT.
-/

/-- Geometry of the streamed representation after `completed` FFT layers.

The layout is used only at boundaries at or after the nonempty unrolled
prefix.  Thus at least one lane bit exists and at least `laneDepth` layers
have completed. -/
structure BoundaryGeometry (depth : Nat) where
  laneDepth : Nat
  completed : HTFFT.Exact.LayerBoundary depth
  laneDepth_pos : 0 < laneDepth
  laneDepth_le_completed : laneDepth ≤ completed.val
  completed_pos : 0 < completed.val

namespace BoundaryGeometry

/-- Boundary geometries are determined by their two computational fields;
the remaining fields are proofs of the admissibility conditions. -/
@[ext] theorem ext {left right : BoundaryGeometry depth}
    (laneDepth : left.laneDepth = right.laneDepth)
    (completed : left.completed = right.completed) : left = right := by
  cases left
  cases right
  simp_all

/-- Number of samples carried in one cycle. -/
def laneCount (geometry : BoundaryGeometry depth) : Nat :=
  2 ^ geometry.laneDepth

/-- Number of cycles carrying one complete FFT vector. -/
def frameLength (geometry : BoundaryGeometry depth) : Nat :=
  2 ^ (depth - geometry.laneDepth)

/-- Number of independent groups at this layer boundary. -/
def groupCount (geometry : BoundaryGeometry depth) : Nat :=
  2 ^ (depth - geometry.completed.val)

/-- Number of cycle positions occupied by one group. -/
def batchCount (geometry : BoundaryGeometry depth) : Nat :=
  2 ^ (geometry.completed.val - geometry.laneDepth)

/-- Number of lanes below the branch-selecting most-significant lane bit. -/
def lanesPerBranch (geometry : BoundaryGeometry depth) : Nat :=
  2 ^ (geometry.laneDepth - 1)

/-- Number of offsets within one half of a completed butterfly layer. -/
def offsetsPerBranch (geometry : BoundaryGeometry depth) : Nat :=
  2 ^ (geometry.completed.val - 1)

@[simp] theorem frameLength_pos (geometry : BoundaryGeometry depth) :
    0 < geometry.frameLength := by
  simp [frameLength]

private theorem completed_le_depth (geometry : BoundaryGeometry depth) :
    geometry.completed.val ≤ depth := by
  omega

private theorem cycle_cardinality (geometry : BoundaryGeometry depth) :
    geometry.groupCount * geometry.batchCount = geometry.frameLength := by
  have exponents :
      depth - geometry.completed.val +
          (geometry.completed.val - geometry.laneDepth) =
        depth - geometry.laneDepth := by
    have completedLe := completed_le_depth geometry
    have laneLe := geometry.laneDepth_le_completed
    omega
  rw [groupCount, batchCount, frameLength, ← Nat.pow_add, exponents]

/-- A complete streamed frame is an integral number of boundary-local
batches, one for each logical group. -/
theorem groupCount_mul_batchCount (geometry : BoundaryGeometry depth) :
    geometry.groupCount * geometry.batchCount = geometry.frameLength :=
  geometry.cycle_cardinality

private theorem lane_cardinality (geometry : BoundaryGeometry depth) :
    2 * geometry.lanesPerBranch = geometry.laneCount := by
  have exponent : geometry.laneDepth - 1 + 1 = geometry.laneDepth := by
    have lanePositive := geometry.laneDepth_pos
    omega
  rw [lanesPerBranch, laneCount]
  calc
    2 * 2 ^ (geometry.laneDepth - 1) =
        2 ^ (geometry.laneDepth - 1) * 2 := by omega
    _ = 2 ^ (geometry.laneDepth - 1 + 1) := by
      rw [Nat.pow_succ]
    _ = 2 ^ geometry.laneDepth := by rw [exponent]

private theorem offset_cardinality (geometry : BoundaryGeometry depth) :
    geometry.batchCount * geometry.lanesPerBranch =
      geometry.offsetsPerBranch := by
  have exponent :
      geometry.completed.val - geometry.laneDepth +
          (geometry.laneDepth - 1) =
        geometry.completed.val - 1 := by
    have lanePositive := geometry.laneDepth_pos
    have laneLe := geometry.laneDepth_le_completed
    omega
  rw [batchCount, lanesPerBranch, offsetsPerBranch, ← Nat.pow_add,
    exponent]

/-- Batch positions and low lane positions form exactly one logical branch
offset. -/
theorem batchCount_mul_lanesPerBranch (geometry : BoundaryGeometry depth) :
    geometry.batchCount * geometry.lanesPerBranch =
      geometry.offsetsPerBranch :=
  geometry.offset_cardinality

private theorem vector_cardinality (geometry : BoundaryGeometry depth) :
    geometry.groupCount * (2 * geometry.offsetsPerBranch) = 2 ^ depth := by
  have branchExponent :
      geometry.completed.val - 1 + 1 = geometry.completed.val := by
    have completedPositive := geometry.completed_pos
    omega
  have totalExponent :
      depth - geometry.completed.val + geometry.completed.val = depth := by
    have := completed_le_depth geometry
    omega
  rw [groupCount, offsetsPerBranch]
  calc
    2 ^ (depth - geometry.completed.val) *
          (2 * 2 ^ (geometry.completed.val - 1)) =
        2 ^ (depth - geometry.completed.val) *
          2 ^ geometry.completed.val := by
      congr 1
      calc
        2 * 2 ^ (geometry.completed.val - 1) =
            2 ^ (geometry.completed.val - 1) * 2 := by omega
        _ = 2 ^ (geometry.completed.val - 1 + 1) := by
          rw [Nat.pow_succ]
        _ = 2 ^ geometry.completed.val := by rw [branchExponent]
    _ = 2 ^ (depth - geometry.completed.val +
          geometry.completed.val) := by
      rw [Nat.pow_add]
    _ = 2 ^ depth := by rw [totalExponent]

/-- Split a physical cycle into its butterfly group and within-group batch. -/
def cycleEquiv (geometry : BoundaryGeometry depth) :
    Fin geometry.frameLength ≃
      Fin geometry.groupCount × Fin geometry.batchCount :=
  (finProdFinEquiv.trans (finCongr geometry.cycle_cardinality)).symm

/-- Split a physical lane into the layer branch and the lane within that
branch. -/
def laneEquiv (geometry : BoundaryGeometry depth) :
    Fin geometry.laneCount ≃ Fin 2 × Fin geometry.lanesPerBranch :=
  (finProdFinEquiv.trans (finCongr geometry.lane_cardinality)).symm

@[simp] theorem cycleEquiv_fst_val (geometry : BoundaryGeometry depth)
    (cycle : Fin geometry.frameLength) :
    (geometry.cycleEquiv cycle).1.val = cycle.val / geometry.batchCount := by
  rfl

@[simp] theorem cycleEquiv_snd_val (geometry : BoundaryGeometry depth)
    (cycle : Fin geometry.frameLength) :
    (geometry.cycleEquiv cycle).2.val = cycle.val % geometry.batchCount := by
  rfl

@[simp] theorem laneEquiv_fst_val (geometry : BoundaryGeometry depth)
    (lane : Fin geometry.laneCount) :
    (geometry.laneEquiv lane).1.val = lane.val / geometry.lanesPerBranch := by
  rfl

@[simp] theorem laneEquiv_snd_val (geometry : BoundaryGeometry depth)
    (lane : Fin geometry.laneCount) :
    (geometry.laneEquiv lane).2.val = lane.val % geometry.lanesPerBranch := by
  rfl

/-- Combine the cycle batch and low lane bits into the offset within one
logical butterfly branch. -/
def offsetEquiv (geometry : BoundaryGeometry depth) :
    Fin geometry.batchCount × Fin geometry.lanesPerBranch ≃
      Fin geometry.offsetsPerBranch :=
  finProdFinEquiv.trans (finCongr geometry.offset_cardinality)

/-- Combine group, branch, and offset into the ordinary logical vector index. -/
def logicalIndexEquiv (geometry : BoundaryGeometry depth) :
    Fin geometry.groupCount × (Fin 2 × Fin geometry.offsetsPerBranch) ≃
      Fin (2 ^ depth) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans
    (finProdFinEquiv.trans (finCongr geometry.vector_cardinality))

/-- Interpret a physical `(cycle, lane)` coordinate as the corresponding
logical index after the selected number of completed layers. -/
def layout (geometry : BoundaryGeometry depth) :
    (Fin geometry.frameLength × Fin geometry.laneCount) ≃ Fin (2 ^ depth) where
  toFun coordinate :=
    let cycle := geometry.cycleEquiv coordinate.1
    let lane := geometry.laneEquiv coordinate.2
    geometry.logicalIndexEquiv
      (cycle.1, lane.1, geometry.offsetEquiv (cycle.2, lane.2))
  invFun index :=
    let logical := geometry.logicalIndexEquiv.symm index
    let offset := geometry.offsetEquiv.symm logical.2.2
    (geometry.cycleEquiv.symm (logical.1, offset.1),
      geometry.laneEquiv.symm (logical.2.1, offset.2))
  left_inv coordinate := by
    rcases coordinate with ⟨cycle, lane⟩
    simp
  right_inv index := by
    simp

/-- Numerical form of the streamed boundary permutation.  A cycle contributes
the group and batch coordinates; a lane contributes the branch bit and its
low lane offset. -/
@[simp] theorem layout_val (geometry : BoundaryGeometry depth)
    (coordinate : Fin geometry.frameLength × Fin geometry.laneCount) :
    let cycle := geometry.cycleEquiv coordinate.1
    let lane := geometry.laneEquiv coordinate.2
    (geometry.layout coordinate).val =
      lane.2.val + geometry.lanesPerBranch * cycle.2.val +
        geometry.offsetsPerBranch * lane.1.val +
          (2 * geometry.offsetsPerBranch) * cycle.1.val := by
  rfl

/-- Physical form of one complete streamed frame at this boundary. -/
abbrev StreamFrame (geometry : BoundaryGeometry depth) (α : Type u) :=
  Silean.FramedLatency.Frame geometry.frameLength
    (Fin geometry.laneCount → α)

/-- Arrange an ordinary logical vector into the streamed boundary layout. -/
def pack (geometry : BoundaryGeometry depth)
    (values : Fin (2 ^ depth) → α) : geometry.StreamFrame α :=
  fun cycle lane => values (geometry.layout (cycle, lane))

/-- Recover an ordinary logical vector from a streamed boundary layout. -/
def unpack (geometry : BoundaryGeometry depth)
    (frame : geometry.StreamFrame α) : Fin (2 ^ depth) → α :=
  fun index =>
    let coordinate := geometry.layout.symm index
    frame coordinate.1 coordinate.2

@[simp] theorem unpack_pack (geometry : BoundaryGeometry depth)
    (values : Fin (2 ^ depth) → α) :
    geometry.unpack (geometry.pack values) = values := by
  funext index
  simp [unpack, pack]

@[simp] theorem pack_unpack (geometry : BoundaryGeometry depth)
    (frame : geometry.StreamFrame α) :
    geometry.pack (geometry.unpack frame) = frame := by
  funext cycle lane
  simp [pack, unpack]

end BoundaryGeometry

/-- Geometry of one shift-register streaming FFT layer.  `laneDepth ≤ stage`
says that all lower layers fit in the parallel unrolled prefix; this stage
pairs values that arrive on different cycles. -/
structure Geometry (depth : Nat) where
  laneDepth : Nat
  stage : Fin depth
  laneDepth_pos : 0 < laneDepth
  laneDepth_le_stage : laneDepth ≤ stage.val

namespace Geometry

/-- Stage geometries are determined by their lane depth and stage; the
remaining fields only certify the admissibility conditions. -/
@[ext] theorem ext {left right : Geometry depth}
    (laneDepth : left.laneDepth = right.laneDepth)
    (stage : left.stage = right.stage) : left = right := by
  cases left
  cases right
  simp_all

/-- Stream layout consumed by this stage, after exactly `stage` layers. -/
def inputBoundary (geometry : Geometry depth) : BoundaryGeometry depth where
  laneDepth := geometry.laneDepth
  completed := ⟨geometry.stage.val, by omega⟩
  laneDepth_pos := geometry.laneDepth_pos
  laneDepth_le_completed := geometry.laneDepth_le_stage
  completed_pos :=
    lt_of_lt_of_le geometry.laneDepth_pos geometry.laneDepth_le_stage

/-- Stream layout produced by this stage, after `stage + 1` layers. -/
def outputBoundary (geometry : Geometry depth) : BoundaryGeometry depth where
  laneDepth := geometry.laneDepth
  completed := ⟨geometry.stage.val + 1, by omega⟩
  laneDepth_pos := geometry.laneDepth_pos
  laneDepth_le_completed :=
    geometry.laneDepth_le_stage.trans (Nat.le_succ geometry.stage.val)
  completed_pos := Nat.succ_pos geometry.stage.val

/-- Cycles in one complete FFT frame. -/
def frameLength (geometry : Geometry depth) : Nat :=
  geometry.inputBoundary.frameLength

/-- Samples carried per cycle. -/
def laneCount (geometry : Geometry depth) : Nat :=
  geometry.inputBoundary.laneCount

/-- Cycles between the two logical halves paired by this layer. -/
def pairDelay (geometry : Geometry depth) : Nat :=
  2 ^ (geometry.stage.val - geometry.laneDepth)

/-- Repeating schedule period of this layer within a complete FFT frame. -/
def localPeriod (geometry : Geometry depth) : Nat :=
  2 ^ (geometry.stage.val + 1 - geometry.laneDepth)

@[simp] theorem input_batchCount (geometry : Geometry depth) :
    geometry.inputBoundary.batchCount = geometry.pairDelay :=
  rfl

@[simp] theorem output_batchCount (geometry : Geometry depth) :
    geometry.outputBoundary.batchCount = geometry.localPeriod :=
  rfl

/-- The two butterfly inputs are separated by half of the stage's repeating
schedule period.  The structural stage realizes this distance with explicit
shift registers. -/
theorem localPeriod_eq_two_mul_pairDelay (geometry : Geometry depth) :
    geometry.localPeriod = 2 * geometry.pairDelay := by
  have exponent :
      geometry.stage.val + 1 - geometry.laneDepth =
        (geometry.stage.val - geometry.laneDepth) + 1 := by
    have laneLe := geometry.laneDepth_le_stage
    omega
  rw [localPeriod, pairDelay, exponent, Nat.pow_succ]
  omega

/-- Geometry of the immediately following streaming layer. -/
def next (geometry : Geometry depth)
    (hasNext : geometry.stage.val + 1 < depth) : Geometry depth where
  laneDepth := geometry.laneDepth
  stage := ⟨geometry.stage.val + 1, hasNext⟩
  laneDepth_pos := geometry.laneDepth_pos
  laneDepth_le_stage :=
    geometry.laneDepth_le_stage.trans (Nat.le_succ geometry.stage.val)

/-- Consecutive stage geometries assign exactly the same meaning to their
shared streamed boundary. -/
@[simp] theorem next_inputBoundary (geometry : Geometry depth)
    (hasNext : geometry.stage.val + 1 < depth) :
    (geometry.next hasNext).inputBoundary = geometry.outputBoundary := by
  cases geometry
  rfl

@[simp] theorem frameLength_pos (geometry : Geometry depth) :
    0 < geometry.frameLength :=
  geometry.inputBoundary.frameLength_pos

@[simp] theorem output_frameLength (geometry : Geometry depth) :
    geometry.outputBoundary.frameLength = geometry.frameLength :=
  rfl

@[simp] theorem output_laneCount (geometry : Geometry depth) :
    geometry.outputBoundary.laneCount = geometry.laneCount :=
  rfl

/-- A complete stage frame consists of one local commutator period for every
output butterfly group. -/
theorem output_groupCount_mul_localPeriod (geometry : Geometry depth) :
    geometry.outputBoundary.groupCount * geometry.localPeriod =
      geometry.frameLength := by
  rw [← geometry.output_batchCount,
    geometry.outputBoundary.groupCount_mul_batchCount]
  rfl

/-- Advancing one FFT layer halves the number of logical groups. -/
theorem input_groupCount_eq_two_mul_output_groupCount
    (geometry : Geometry depth) :
    geometry.inputBoundary.groupCount =
      2 * geometry.outputBoundary.groupCount := by
  change 2 ^ (depth - geometry.stage.val) =
    2 * 2 ^ (depth - (geometry.stage.val + 1))
  have stageLt := geometry.stage.isLt
  have exponent :
      depth - geometry.stage.val =
        (depth - (geometry.stage.val + 1)) + 1 := by
    omega
  rw [exponent, Nat.pow_succ]
  omega

end Geometry

end HTFFT.Silean.FFTStage
