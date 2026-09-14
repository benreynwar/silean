import Silean.Examples.PicoRV.Memory.MemoryBasicUpdates
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified

namespace Silean.Examples.PicoRV.Memory.ProofSupport

open Silean

theorem splitValue_eq_unpack (signals : SignalMap.{0})
    (value : signals.tupleType.Denote) :
    Modules.NamedTupleSplitter.splitValue signals value = signals.unpack value := by
  calc
    Modules.NamedTupleSplitter.splitValue signals value =
        Modules.NamedTupleSplitter.splitValue signals
          (signals.pack (signals.unpack value)) := by rw [signals.pack_unpack]
    _ = signals.unpack value :=
      Modules.NamedTupleSplitter.splitValue_pack signals _

theorem equal_stateOfNat (bits : TwoBits) (value : Nat)
    (bound : value < 4) :
    (SignalType.vector 2 .bit).equal bits (stateOfNat value) =
      decide (BitVector.toNat 2 bits = value) := by
  have encoded : BitVector.toNat 2 (stateOfNat value) = value := by
    rw [show stateOfNat value = BitVector.ofNat 2 value by rfl]
    rw [BitVector.toNat_ofNat, BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt bound]
  by_cases matched : BitVector.toNat 2 bits = value
  · have bitsEqual : bits = stateOfNat value := by
      apply BitVector.toNat_injective 2
      simpa [encoded] using matched
    rw [((SignalType.vector 2 .bit).equal_eq_true_iff _ _).mpr bitsEqual]
    simp [matched]
  · have bitsDifferent : bits ≠ stateOfNat value := by
      intro equal
      apply matched
      rw [equal, encoded]
    simp only [matched]
    cases left : (SignalType.vector 2 .bit).equal bits (stateOfNat value)
    · rfl
    · exact (bitsDifferent
        (((SignalType.vector 2 .bit).equal_eq_true_iff _ _).mp left)).elim

end Silean.Examples.PicoRV.Memory.ProofSupport
