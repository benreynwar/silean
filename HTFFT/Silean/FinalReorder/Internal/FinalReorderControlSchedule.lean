import HTFFT.Silean.FinalReorder.Control.ControlAddress
import HTFFT.Silean.FinalReorder.Control.ControlFrame
import HTFFT.Silean.FinalReorder.Internal.FinalReorderStructure

/-! Bridge from the controller's bit-vector outputs to the pure two-bank
final-reorder schedule. -/

namespace HTFFT.Silean.FinalReorder.Internal
open FFT

open _root_.Silean

theorem addressCardinality (configuration : Configuration depth) :
    BitVector.cardinality (addressWidth configuration) =
      configuration.frameLength := by
  simp [addressWidth, Configuration.frameLength,
    BitVector.cardinality_eq_pow]

theorem addressHalfCardinality (configuration : Configuration depth) :
    BitVector.cardinality (addressWidth configuration - 1) =
      halfFrameLength configuration := by
  simp [addressWidth, halfFrameLength, Configuration.finalReorderLatency,
    BitVector.cardinality_eq_pow]

def expectedWriteControls (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    FinalReorder.Control.WriteObservation (addressWidth configuration) where
  address0 := BitVector.ofNat (addressWidth configuration)
    (firstBankWriteAddress configuration cycle).val
  address1 := BitVector.ofNat (addressWidth configuration)
    (secondBankWriteAddress configuration cycle).val
  swap := decide (cycle.val % 2 = 1)
  bypass := decide (cycle.val + 1 = configuration.frameLength)

def expectedReadControls (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    FinalReorder.Control.ReadObservation (addressWidth configuration) where
  address := BitVector.ofNat (addressWidth configuration) cycle.val
  swap := decide (halfFrameLength configuration ≤ cycle.val)

theorem writeControls_of_cycle (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    FinalReorder.Control.writeControls (addressWidth configuration)
        (BitVector.ofNat (addressWidth configuration) cycle.val) =
      expectedWriteControls configuration cycle := by
  have positive := addressWidth_pos configuration
  have cycleBound : cycle.val <
      BitVector.cardinality (addressWidth configuration) := by
    rw [addressCardinality]
    exact cycle.isLt
  have remainderBound : cycle.val % 2 < 2 := Nat.mod_lt _ (by omega)
  have firstAddressBound :
      (firstBankWriteAddress configuration cycle).val <
        BitVector.cardinality (addressWidth configuration) := by
    rw [addressCardinality]
    exact (firstBankWriteAddress configuration cycle).isLt
  have secondAddressBound :
      (secondBankWriteAddress configuration cycle).val <
        BitVector.cardinality (addressWidth configuration) := by
    rw [addressCardinality]
    exact (secondBankWriteAddress configuration cycle).isLt
  apply FinalReorder.Control.WriteObservation.ext
  · change FinalReorder.Control.writeAddress0 _ _ =
        BitVector.ofNat _ (firstBankWriteAddress configuration cycle).val
    apply BitVector.toNat_injective
    rw [FinalReorder.Control.toNat_writeAddress0 _ positive]
    rw [BitVector.toNat_ofNat, Nat.mod_eq_of_lt cycleBound]
    rw [FinalReorder.Control.lowBit_ofNat _ _ positive]
    rw [addressHalfCardinality]
    rw [BitVector.toNat_ofNat, Nat.mod_eq_of_lt firstAddressBound]
    unfold firstBankWriteAddress
    by_cases even : cycle.val % 2 = 0
    · have notOdd : cycle.val % 2 ≠ 1 := by omega
      rw [dif_pos even]
      simp [notOdd]
    · have odd : cycle.val % 2 = 1 := by omega
      rw [dif_neg even]
      simp [odd]
  · change FinalReorder.Control.writeAddress1 _ _ =
        BitVector.ofNat _ (secondBankWriteAddress configuration cycle).val
    apply BitVector.toNat_injective
    rw [FinalReorder.Control.toNat_writeAddress1 _ positive]
    rw [BitVector.toNat_ofNat, Nat.mod_eq_of_lt cycleBound]
    rw [FinalReorder.Control.lowBit_ofNat _ _ positive]
    rw [addressHalfCardinality]
    rw [BitVector.toNat_ofNat, Nat.mod_eq_of_lt secondAddressBound]
    unfold secondBankWriteAddress
    by_cases even : cycle.val % 2 = 0
    · have notOdd : cycle.val % 2 ≠ 1 := by omega
      rw [dif_pos even]
      simp [notOdd]
    · have odd : cycle.val % 2 = 1 := by omega
      rw [dif_neg even]
      simp [odd]
  · change FinalReorder.Control.lowBit _ _ = decide (cycle.val % 2 = 1)
    exact FinalReorder.Control.lowBit_ofNat _ _ positive
  · change FinalReorder.Control.bypass _ _ =
        decide (cycle.val + 1 = configuration.frameLength)
    rw [FinalReorder.Control.bypass_ofNat _ _ cycleBound,
      addressCardinality]
    apply Bool.eq_iff_iff.mpr
    simp
    omega

theorem readControls_of_cycle (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    FinalReorder.Control.readControls (addressWidth configuration)
        (BitVector.ofNat (addressWidth configuration) cycle.val) =
      expectedReadControls configuration cycle := by
  have positive := addressWidth_pos configuration
  have cycleBound : cycle.val <
      BitVector.cardinality (addressWidth configuration) := by
    rw [addressCardinality]
    exact cycle.isLt
  apply FinalReorder.Control.ReadObservation.ext
  · change FinalReorder.Control.readAddress _ _ = _
    rfl
  · change FinalReorder.Control.highBit _ _ =
        decide (halfFrameLength configuration ≤ cycle.val)
    rw [FinalReorder.Control.highBit_ofNat _ _ positive cycleBound,
      addressHalfCardinality]

end HTFFT.Silean.FinalReorder.Internal
