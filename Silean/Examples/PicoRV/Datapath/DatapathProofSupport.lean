import Silean.Examples.PicoRV.Datapath.DatapathBasicUpdates
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace Silean.Examples.PicoRV.Datapath.ProofSupport

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

theorem lowFive_layout (word : Word) :
    Modules.VectorLayout.apply LoadRs2Update.lowFiveLayout word = lowFiveBits word := by
  rfl

theorem addBits_eq_addWords (left right : Word) :
    (Modules.Add.addBits 32 left right false).1 = addWords left right := by
  apply BitVector.toNat_injective 32
  have numeric := Modules.Add.addBits_numeric 32 left right false
  simp only [Bool.toNat_false, Nat.add_zero] at numeric
  have resultBound := BitVector.toNat_lt_cardinality 32
    (Modules.Add.addBits 32 left right false).1
  have outputToNat : BitVector.toNat 32 (addWords left right) =
      (BitVector.toNat 32 left + BitVector.toNat 32 right) %
        BitVector.cardinality 32 := by
    rw [show addWords left right = BitVector.ofNat 32
        (BitVector.toNat 32 left + BitVector.toNat 32 right) by rfl]
    exact BitVector.toNat_ofNat 32 _
  rw [outputToNat]
  cases carry : (Modules.Add.addBits 32 left right false).2
  · simp only [carry, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at numeric
    rw [← numeric, Nat.mod_eq_of_lt resultBound]
  · simp only [carry, Bool.toNat_true, Nat.mul_one] at numeric
    rw [← numeric, Nat.add_mod, Nat.mod_eq_of_lt resultBound, Nat.mod_self,
      Nat.add_zero]
    rw [Nat.mod_eq_of_lt resultBound]

end Silean.Examples.PicoRV.Datapath.ProofSupport
