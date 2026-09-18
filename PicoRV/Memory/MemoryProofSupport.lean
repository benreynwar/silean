import PicoRV.Memory.MemoryBasicUpdates
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace PicoRV.Memory.ProofSupport

open Silean

theorem splitValue_eq_unpack (signals : Silean.SignalMap.{0})
    (value : signals.tupleType.Denote) :
    Silean.Modules.NamedTupleSplitter.splitValue signals value = signals.unpack value := by
  calc
    Silean.Modules.NamedTupleSplitter.splitValue signals value =
        Silean.Modules.NamedTupleSplitter.splitValue signals
          (signals.pack (signals.unpack value)) := by rw [signals.pack_unpack]
    _ = signals.unpack value :=
      Silean.Modules.NamedTupleSplitter.splitValue_pack signals _

theorem equal_stateOfNat (bits : TwoBits) (value : Nat)
    (bound : value < 4) :
    (Silean.SignalType.vector 2 .bit).equal bits (stateOfNat value) =
      decide (Silean.BitVector.toNat 2 bits = value) := by
  have encoded : Silean.BitVector.toNat 2 (stateOfNat value) = value := by
    rw [show stateOfNat value = Silean.BitVector.ofNat 2 value by rfl]
    rw [Silean.BitVector.toNat_ofNat, Silean.BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt bound]
  by_cases matched : Silean.BitVector.toNat 2 bits = value
  · have bitsEqual : bits = stateOfNat value := by
      apply Silean.BitVector.toNat_injective 2
      simpa [encoded] using matched
    rw [((Silean.SignalType.vector 2 .bit).equal_eq_true_iff _ _).mpr bitsEqual]
    simp [matched]
  · have bitsDifferent : bits ≠ stateOfNat value := by
      intro equal
      apply matched
      rw [equal, encoded]
    simp only [matched]
    cases left : (Silean.SignalType.vector 2 .bit).equal bits (stateOfNat value)
    · rfl
    · exact (bitsDifferent
        (((Silean.SignalType.vector 2 .bit).equal_eq_true_iff _ _).mp left)).elim

end PicoRV.Memory.ProofSupport
