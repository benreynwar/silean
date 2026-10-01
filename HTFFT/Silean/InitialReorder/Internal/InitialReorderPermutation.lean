import HTFFT.Silean.InitialReorder.Lane.Lane

/-! Pure address arithmetic behind the VHDL initial reorder. -/

namespace HTFFT.Silean.InitialReorder.Internal
open FFT

open _root_.Silean
open _root_.Silean.Modules

abbrev LongAddress (configuration : Configuration depth) :=
  Fin (configuration.laneDepth + InitialReorder.addressWidth configuration) →
    Bool

def lowLaneBits (configuration : Configuration depth)
    (address : LongAddress configuration) :
    Fin configuration.laneDepth → Bool :=
  fun index => address (Fin.castAdd (InitialReorder.addressWidth configuration) index)

def highCycleBits (configuration : Configuration depth)
    (address : LongAddress configuration) :
    Fin (InitialReorder.addressWidth configuration) → Bool :=
  fun index => address (Fin.natAdd configuration.laneDepth index)

theorem concat_low_high (configuration : Configuration depth)
    (address : LongAddress configuration) :
    VectorConcat.concat (lowLaneBits configuration address)
      (highCycleBits configuration address) = address := by
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro low
    simp [lowLaneBits]
  · intro high
    simp [highCycleBits]

def cycleAddress (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    Fin (InitialReorder.addressWidth configuration) → Bool :=
  BitVector.ofNat (InitialReorder.addressWidth configuration) cycle.val

def reversedLongAddress (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) : LongAddress configuration :=
  InitialReorder.Lane.reverseLongAddress configuration
    (InitialReorder.Lane.longAddress configuration lane
      (cycleAddress configuration cycle))

def reversedLane (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) : Fin configuration.laneCount :=
  Fin.cast (BitVector.cardinality_eq_pow configuration.laneDepth)
    (BitVector.toIndex configuration.laneDepth
      (lowLaneBits configuration (reversedLongAddress configuration cycle lane)))

def reversedCycle (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) : Fin configuration.frameLength :=
  Fin.cast (BitVector.cardinality_eq_pow
    (InitialReorder.addressWidth configuration))
    (BitVector.toIndex (InitialReorder.addressWidth configuration)
      (highCycleBits configuration
        (reversedLongAddress configuration cycle lane)))

@[simp] theorem cycleAddress_reversedCycle (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    cycleAddress configuration (reversedCycle configuration cycle lane) =
      highCycleBits configuration
        (reversedLongAddress configuration cycle lane) := by
  unfold cycleAddress reversedCycle
  simp only [Fin.val_cast, BitVector.ofNat_toIndex]

@[simp] theorem laneBits_reversedLane (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    BitVector.ofNat configuration.laneDepth
        (reversedLane configuration cycle lane).val =
      lowLaneBits configuration
        (reversedLongAddress configuration cycle lane) := by
  unfold reversedLane
  simp only [Fin.val_cast, BitVector.ofNat_toIndex]

/-- Reassembling the two physical coordinates obtained from the reversed
address recovers that complete reversed address. -/
theorem longAddress_reversedCoordinate
    (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    InitialReorder.Lane.longAddress configuration
        (reversedLane configuration cycle lane)
        (cycleAddress configuration (reversedCycle configuration cycle lane)) =
      reversedLongAddress configuration cycle lane := by
  unfold InitialReorder.Lane.longAddress
  rw [laneBits_reversedLane, cycleAddress_reversedCycle]
  exact concat_low_high configuration _

/-- Reversing the reconstructed reversed coordinate returns the original
complete logical address. -/
theorem reverse_reversedCoordinate (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    InitialReorder.Lane.reverseLongAddress configuration
      (InitialReorder.Lane.longAddress configuration
        (reversedLane configuration cycle lane)
        (cycleAddress configuration (reversedCycle configuration cycle lane))) =
      InitialReorder.Lane.longAddress configuration lane
        (cycleAddress configuration cycle) := by
  rw [longAddress_reversedCoordinate]
  unfold reversedLongAddress InitialReorder.Lane.reverseLongAddress
  funext index
  simp

/-- The two address orientations select matching locations for a coordinate
and its global bit reversal. -/
theorem memoryAddress_opposite (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount)
    (reversed : Bool) :
    InitialReorder.Lane.memoryAddress configuration
        (reversedLane configuration cycle lane)
        (cycleAddress configuration (reversedCycle configuration cycle lane))
        (!reversed) =
      InitialReorder.Lane.memoryAddress configuration lane
        (cycleAddress configuration cycle) reversed := by
  cases reversed with
  | false =>
      simp only [Bool.not_false, InitialReorder.Lane.memoryAddress,
        Bool.cond_true, Bool.cond_false]
      rw [reverse_reversedCoordinate]
  | true =>
      simp only [Bool.not_true, InitialReorder.Lane.memoryAddress,
        Bool.cond_true, Bool.cond_false]
      rw [longAddress_reversedCoordinate]
      rfl

/-- The pre/post rotation amount is the lane component of the globally
bit-reversed coordinate. -/
theorem laneRotation_eq_reversedLaneBits
    (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    InitialReorder.laneRotation configuration
        (cycleAddress configuration cycle) =
      lowLaneBits configuration
        (reversedLongAddress configuration cycle lane) := by
  funext index
  unfold InitialReorder.laneRotation cycleAddress lowLaneBits
    reversedLongAddress InitialReorder.Lane.reverseLongAddress
    InitialReorder.Lane.longAddress
  let cycleIndex : Fin (InitialReorder.addressWidth configuration) :=
    ⟨InitialReorder.addressWidth configuration - 1 - index.val, by
      have fits := InitialReorder.laneDepth_le_addressWidth configuration
      have indexLt := index.isLt
      omega⟩
  have reversedIndex :
      (Fin.castAdd (InitialReorder.addressWidth configuration) index).rev =
        Fin.natAdd configuration.laneDepth cycleIndex := by
    apply Fin.ext
    simp [cycleIndex]
    have indexWithinAddress :
        index.val + 1 ≤ InitialReorder.addressWidth configuration := by
      have fits := InitialReorder.laneDepth_le_addressWidth configuration
      have indexLt := index.isLt
      omega
    omega
  rw [reversedIndex]
  rw [VectorConcat.concat_right]
  rfl

theorem laneRotation_reversed_eq_laneBits
    (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    InitialReorder.laneRotation configuration
        (cycleAddress configuration
          (reversedCycle configuration cycle lane)) =
      BitVector.ofNat configuration.laneDepth lane.val := by
  rw [laneRotation_eq_reversedLaneBits configuration
    (reversedCycle configuration cycle lane)
    (reversedLane configuration cycle lane)]
  have reversedAgain := congrArg (lowLaneBits configuration)
    (reverse_reversedCoordinate configuration cycle lane)
  unfold reversedLongAddress
  rw [reversedAgain]
  funext index
  unfold lowLaneBits InitialReorder.Lane.longAddress
  rw [VectorConcat.concat_left]

theorem laneRotation_toNat (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    BitVector.toNat configuration.laneDepth
        (InitialReorder.laneRotation configuration
          (cycleAddress configuration cycle)) =
      (reversedLane configuration cycle lane).val := by
  rw [laneRotation_eq_reversedLaneBits configuration cycle lane]
  unfold reversedLane
  simp only [Fin.val_cast, BitVector.toIndex_val]

theorem reversed_laneRotation_toNat (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    BitVector.toNat configuration.laneDepth
        (InitialReorder.laneRotation configuration
          (cycleAddress configuration
            (reversedCycle configuration cycle lane))) = lane.val := by
  rw [laneRotation_reversed_eq_laneBits, BitVector.toNat_ofNat,
    BitVector.cardinality_eq_pow, Nat.mod_eq_of_lt lane.isLt]

def bankIndex (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) : Fin configuration.laneCount :=
  BarrelShifter.rotateSourceIndex configuration.laneDepth
    (BitVector.toNat configuration.laneDepth
      (InitialReorder.laneRotation configuration
        (cycleAddress configuration cycle))) lane

/-- The bank mapping is invariant under global bit reversal.  This is the key
reason the VHDL architecture can alternate natural and reversed addresses in
one set of memories. -/
theorem bankIndex_reversed (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    bankIndex configuration (reversedCycle configuration cycle lane)
        (reversedLane configuration cycle lane) =
      bankIndex configuration cycle lane := by
  apply Fin.ext
  unfold bankIndex BarrelShifter.rotateSourceIndex
  rw [reversed_laneRotation_toNat configuration cycle lane,
    laneRotation_toNat configuration cycle lane]
  simp only [Nat.add_comm]

/-- The encoded pre-rotation is the additive inverse of the positive lane
rotation in the power-of-two lane ring. -/
theorem preRotation_toNat (configuration : Configuration depth)
    (address : Fin (InitialReorder.addressWidth configuration) → Bool) :
    BitVector.toNat configuration.laneDepth
        (InitialReorder.preRotation configuration address) =
      (configuration.laneCount -
        BitVector.toNat configuration.laneDepth
          (InitialReorder.laneRotation configuration address)) %
        configuration.laneCount := by
  unfold InitialReorder.preRotation ConditionalNegate.resultValue
  simp only [cond_true, BitVector.toNat_ofBitVec, BitVec.toNat_neg,
    BitVector.toBitVec_toNat, Configuration.laneCount]

/-- Pre-rotating the logical lane vector places lane `lane` in its symmetric
bank index. -/
theorem preRotation_sourceIndex (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    BarrelShifter.sourceIndex configuration.laneDepth
        (InitialReorder.preRotation configuration
          (cycleAddress configuration cycle))
        (bankIndex configuration cycle lane) = lane := by
  apply Fin.ext
  unfold BarrelShifter.sourceIndex BarrelShifter.rotateSourceIndex bankIndex
  rw [preRotation_toNat]
  let rotation := BitVector.toNat configuration.laneDepth
    (InitialReorder.laneRotation configuration
      (cycleAddress configuration cycle))
  change (((lane.val + rotation) % configuration.laneCount +
      ((configuration.laneCount - rotation) % configuration.laneCount)) %
        configuration.laneCount) = lane.val
  have rotationLt : rotation < configuration.laneCount := by
    dsimp only [rotation]
    simpa [Configuration.laneCount] using
      BitVector.toNat_lt_cardinality configuration.laneDepth
        (InitialReorder.laneRotation configuration
          (cycleAddress configuration cycle))
  have laneLt : lane.val < configuration.laneCount := lane.isLt
  by_cases rotationZero : rotation = 0
  · simp [rotationZero, Nat.mod_eq_of_lt laneLt]
  · have rotationPositive : 0 < rotation := Nat.pos_of_ne_zero rotationZero
    have differenceLt : configuration.laneCount - rotation <
        configuration.laneCount := by omega
    rw [Nat.mod_eq_of_lt differenceLt]
    have combine := Nat.add_mod (lane.val + rotation)
      (configuration.laneCount - rotation) configuration.laneCount
    rw [Nat.mod_eq_of_lt differenceLt] at combine
    rw [combine.symm]
    have sumEqual : lane.val + rotation +
        (configuration.laneCount - rotation) =
          lane.val + configuration.laneCount := by omega
    rw [sumEqual]
    simp [Nat.mod_eq_of_lt laneLt]

/-- The bank permutation and its negative-rotation source selection are
mutual inverses. -/
theorem bankIndex_preRotation_source
    (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (bank : Fin configuration.laneCount) :
    bankIndex configuration cycle
        (BarrelShifter.sourceIndex configuration.laneDepth
          (InitialReorder.preRotation configuration
            (cycleAddress configuration cycle)) bank) = bank := by
  let assign := bankIndex configuration cycle
  have assignInjective : Function.Injective assign := by
    intro first second equal
    calc
      first = BarrelShifter.sourceIndex configuration.laneDepth
          (InitialReorder.preRotation configuration
            (cycleAddress configuration cycle)) (assign first) :=
        (preRotation_sourceIndex configuration cycle first).symm
      _ = BarrelShifter.sourceIndex configuration.laneDepth
          (InitialReorder.preRotation configuration
            (cycleAddress configuration cycle)) (assign second) := by
        rw [equal]
      _ = second := preRotation_sourceIndex configuration cycle second
  obtain ⟨lane, rfl⟩ := Finite.surjective_of_injective assignInjective bank
  rw [preRotation_sourceIndex]

theorem preRotation_result_at_bankIndex
    (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (values : Fin configuration.laneCount → α)
    (lane : Fin configuration.laneCount) :
    BarrelShifter.resultValue configuration.laneDepth
        (InitialReorder.preRotation configuration
          (cycleAddress configuration cycle)) values
        (bankIndex configuration cycle lane) = values lane := by
  rw [BarrelShifter.resultValue_at, preRotation_sourceIndex]

/-- The positive post-rotation selects the symmetric bank for each output
lane. -/
theorem postRotation_result_at_lane
    (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (values : Fin configuration.laneCount → α)
    (lane : Fin configuration.laneCount) :
    BarrelShifter.resultValue configuration.laneDepth
        (InitialReorder.laneRotation configuration
          (cycleAddress configuration cycle)) values lane =
      values (bankIndex configuration cycle lane) := by
  rfl

/-- In natural-address orientation, the per-bank address is exactly the
frame-cycle address. -/
theorem memoryAddress_false (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    InitialReorder.Lane.memoryAddress configuration lane
        (cycleAddress configuration cycle) false =
      cycleAddress configuration cycle := by
  funext index
  simp [InitialReorder.Lane.memoryAddress, VectorSlice.slice,
    InitialReorder.Lane.longAddress, VectorConcat.concat]

theorem cycleAddress_injective (configuration : Configuration depth) :
    Function.Injective (cycleAddress configuration) := by
  intro first second equal
  apply Fin.ext
  have numeric := congrArg
    (BitVector.toNat (InitialReorder.addressWidth configuration)) equal
  simpa [cycleAddress, BitVector.cardinality_eq_pow,
    Nat.mod_eq_of_lt first.isLt, Nat.mod_eq_of_lt second.isLt] using numeric

theorem bankAddress_false_injective (configuration : Configuration depth)
    {firstCycle secondCycle : Fin configuration.frameLength}
    {firstLane secondLane : Fin configuration.laneCount}
    (bankEqual : bankIndex configuration firstCycle firstLane =
      bankIndex configuration secondCycle secondLane)
    (addressEqual :
      InitialReorder.Lane.memoryAddress configuration firstLane
          (cycleAddress configuration firstCycle) false =
        InitialReorder.Lane.memoryAddress configuration secondLane
          (cycleAddress configuration secondCycle) false) :
    firstCycle = secondCycle ∧ firstLane = secondLane := by
  have cycleEqual : firstCycle = secondCycle :=
    cycleAddress_injective configuration (by
      simpa only [memoryAddress_false] using addressEqual)
  subst secondCycle
  have laneEqual : firstLane = secondLane := by
    calc
      firstLane = BarrelShifter.sourceIndex configuration.laneDepth
          (InitialReorder.preRotation configuration
            (cycleAddress configuration firstCycle))
          (bankIndex configuration firstCycle firstLane) :=
        (preRotation_sourceIndex configuration firstCycle firstLane).symm
      _ = BarrelShifter.sourceIndex configuration.laneDepth
          (InitialReorder.preRotation configuration
            (cycleAddress configuration firstCycle))
          (bankIndex configuration firstCycle secondLane) := by
        rw [bankEqual]
      _ = secondLane :=
        preRotation_sourceIndex configuration firstCycle secondLane
  exact ⟨rfl, laneEqual⟩

theorem toBitVec_reverseLongAddress (configuration : Configuration depth)
    (address : LongAddress configuration) :
    BitVector.toBitVec
        (configuration.laneDepth + InitialReorder.addressWidth configuration)
        (InitialReorder.Lane.reverseLongAddress configuration address) =
      (BitVector.toBitVec
        (configuration.laneDepth + InitialReorder.addressWidth configuration)
        address).reverse := by
  apply BitVec.eq_of_getElem_eq_iff.mpr
  intro index inBounds
  rw [BitVec.getElem_reverse]
  change (BitVector.toBitVec
      (configuration.laneDepth + InitialReorder.addressWidth configuration)
      (InitialReorder.Lane.reverseLongAddress configuration address)).getLsb
        ⟨index, inBounds⟩ = _
  rw [BitVector.getLsb_toBitVec]
  unfold InitialReorder.Lane.reverseLongAddress
  rw [BitVec.getMsbD_eq_getLsbD]
  simp only [inBounds, decide_true, Bool.true_and]
  have reversedInBounds :
      configuration.laneDepth + InitialReorder.addressWidth configuration - 1 -
          index <
        configuration.laneDepth + InitialReorder.addressWidth configuration := by
    omega
  rw [BitVec.getLsbD_eq_getElem reversedInBounds]
  rw [← BitVector.getLsb_toBitVec
    (configuration.laneDepth + InitialReorder.addressWidth configuration)
    address]
  congr 1
  apply Fin.ext
  simp
  omega

def packedIndex (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    Fin (2 ^ (configuration.laneDepth +
      InitialReorder.addressWidth configuration)) :=
  (BitVector.toBitVec
    (configuration.laneDepth + InitialReorder.addressWidth configuration)
    (InitialReorder.Lane.longAddress configuration lane
      (cycleAddress configuration cycle))).toFin

/-- The coordinate reconstructed from the reversed address really denotes the
native bit reversal of the original packed index. -/
theorem packedIndex_reversed (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    packedIndex configuration (reversedCycle configuration cycle lane)
        (reversedLane configuration cycle lane) =
      HTFFT.Exact.bitReverseIndex (packedIndex configuration cycle lane) := by
  unfold packedIndex HTFFT.Exact.bitReverseIndex
  rw [longAddress_reversedCoordinate configuration cycle lane]
  unfold reversedLongAddress
  rw [toBitVec_reverseLongAddress]

theorem packedIndex_val (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    (packedIndex configuration cycle lane).val =
      (naturalLayout configuration (cycle, lane)).val := by
  unfold packedIndex
  simp only [BitVec.val_toFin, BitVector.toBitVec_toNat]
  unfold InitialReorder.Lane.longAddress
  rw [VectorConcat.toNat_concat]
  simp only [BitVector.toNat_ofNat, BitVector.cardinality_eq_pow,
    naturalLayout_val]
  rw [Nat.mod_eq_of_lt lane.isLt]
  unfold cycleAddress
  rw [BitVector.toNat_ofNat, BitVector.cardinality_eq_pow,
    Nat.mod_eq_of_lt cycle.isLt]

theorem totalWidth_eq_depth (configuration : Configuration depth) :
    configuration.laneDepth + InitialReorder.addressWidth configuration =
      depth := by
  unfold InitialReorder.addressWidth
  exact Nat.add_sub_of_le configuration.laneDepth_le_depth

def packedToGlobal (configuration : Configuration depth) :
    Fin (2 ^ (configuration.laneDepth +
      InitialReorder.addressWidth configuration)) → Fin (2 ^ depth) :=
  Fin.cast (congrArg (2 ^ ·) (totalWidth_eq_depth configuration))

theorem packedToGlobal_packedIndex (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    packedToGlobal configuration (packedIndex configuration cycle lane) =
      naturalLayout configuration (cycle, lane) := by
  apply Fin.ext
  exact packedIndex_val configuration cycle lane

theorem packedToGlobal_bitReverse (configuration : Configuration depth)
    (index : Fin (2 ^ (configuration.laneDepth +
      InitialReorder.addressWidth configuration))) :
    packedToGlobal configuration (HTFFT.Exact.bitReverseIndex index) =
      HTFFT.Exact.bitReverseIndex (packedToGlobal configuration index) := by
  exact bitReverseIndex_cast (totalWidth_eq_depth configuration) index
where
  bitReverseIndex_cast {left right : Nat} (equal : left = right)
      (value : Fin (2 ^ left)) :
      Fin.cast (congrArg (2 ^ ·) equal)
          (HTFFT.Exact.bitReverseIndex value) =
        HTFFT.Exact.bitReverseIndex
          (Fin.cast (congrArg (2 ^ ·) equal) value) := by
    subst right
    rfl

/-- `reversedCycle` and `reversedLane` are exactly the physical coordinates
of the complete global bit-reversed index used by the public contract. -/
theorem naturalLayout_reversed (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    naturalLayout configuration
        (reversedCycle configuration cycle lane,
          reversedLane configuration cycle lane) =
      HTFFT.Exact.bitReverseIndex
        (naturalLayout configuration (cycle, lane)) := by
  rw [← packedToGlobal_packedIndex configuration
    (reversedCycle configuration cycle lane)
    (reversedLane configuration cycle lane)]
  rw [packedIndex_reversed]
  rw [packedToGlobal_bitReverse]
  rw [packedToGlobal_packedIndex]

/-- With one fixed address orientation, a bank number and its local memory
address uniquely identify the logical cycle/lane coordinate. -/
theorem bankAddress_injective (configuration : Configuration depth)
    (reversed : Bool)
    {firstCycle secondCycle : Fin configuration.frameLength}
    {firstLane secondLane : Fin configuration.laneCount}
    (bankEqual : bankIndex configuration firstCycle firstLane =
      bankIndex configuration secondCycle secondLane)
    (addressEqual :
      InitialReorder.Lane.memoryAddress configuration firstLane
          (cycleAddress configuration firstCycle) reversed =
        InitialReorder.Lane.memoryAddress configuration secondLane
          (cycleAddress configuration secondCycle) reversed) :
    firstCycle = secondCycle ∧ firstLane = secondLane := by
  cases reversed with
  | false =>
      exact bankAddress_false_injective configuration bankEqual addressEqual
  | true =>
      have reversedBankEqual :
          bankIndex configuration
              (reversedCycle configuration firstCycle firstLane)
              (reversedLane configuration firstCycle firstLane) =
            bankIndex configuration
              (reversedCycle configuration secondCycle secondLane)
              (reversedLane configuration secondCycle secondLane) := by
        simpa only [bankIndex_reversed] using bankEqual
      have reversedAddressEqual :
          InitialReorder.Lane.memoryAddress configuration
              (reversedLane configuration firstCycle firstLane)
              (cycleAddress configuration
                (reversedCycle configuration firstCycle firstLane)) false =
            InitialReorder.Lane.memoryAddress configuration
              (reversedLane configuration secondCycle secondLane)
              (cycleAddress configuration
                (reversedCycle configuration secondCycle secondLane)) false := by
        calc
          _ = InitialReorder.Lane.memoryAddress configuration firstLane
              (cycleAddress configuration firstCycle) true := by
            simpa using memoryAddress_opposite configuration firstCycle
              firstLane true
          _ = InitialReorder.Lane.memoryAddress configuration secondLane
              (cycleAddress configuration secondCycle) true := addressEqual
          _ = _ := by
            simpa using (memoryAddress_opposite configuration secondCycle
              secondLane true).symm
      have reversedCoordinateEqual := bankAddress_false_injective configuration
        reversedBankEqual reversedAddressEqual
      have layoutEqual :
          HTFFT.Exact.bitReverseIndex
              (naturalLayout configuration (firstCycle, firstLane)) =
            HTFFT.Exact.bitReverseIndex
              (naturalLayout configuration (secondCycle, secondLane)) := by
        rw [← naturalLayout_reversed configuration firstCycle firstLane,
          ← naturalLayout_reversed configuration secondCycle secondLane,
          reversedCoordinateEqual.1, reversedCoordinateEqual.2]
      have naturalEqual :=
        HTFFT.Exact.bitReverseIndex_involutive.injective layoutEqual
      have coordinateEqual :=
        (naturalLayout configuration).injective naturalEqual
      exact ⟨congrArg Prod.fst coordinateEqual,
        congrArg Prod.snd coordinateEqual⟩

theorem resultFrame_at (configuration : Configuration depth)
    (input : InputFrame configuration)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    InitialReorder.resultFrame configuration input cycle lane =
      input (reversedCycle configuration cycle lane)
        (reversedLane configuration cycle lane) := by
  unfold InitialReorder.resultFrame HTFFT.Exact.bitReverse
    unpackInput unpackNatural
  have coordinate := naturalLayout_reversed configuration cycle lane
  rw [← coordinate]
  simp

end HTFFT.Silean.InitialReorder.Internal
