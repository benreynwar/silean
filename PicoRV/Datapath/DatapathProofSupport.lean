import PicoRV.Datapath.DatapathBasicUpdates
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace PicoRV.Datapath.ProofSupport

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

theorem lowFive_layout (word : Word) :
    Silean.Modules.VectorLayout.apply LoadRs2Update.lowFiveLayout word = lowFiveBits word := by
  rfl

theorem addBits_eq_addWords (left right : Word) :
    (Silean.Modules.Add.addBits 32 left right false).1 = addWords left right := by
  apply Silean.BitVector.toNat_injective 32
  have numeric := Silean.Modules.Add.addBits_numeric 32 left right false
  simp only [Bool.toNat_false, Nat.add_zero] at numeric
  have resultBound := Silean.BitVector.toNat_lt_cardinality 32
    (Silean.Modules.Add.addBits 32 left right false).1
  have outputToNat : Silean.BitVector.toNat 32 (addWords left right) =
      (Silean.BitVector.toNat 32 left + Silean.BitVector.toNat 32 right) %
        Silean.BitVector.cardinality 32 := by
    rw [show addWords left right = Silean.BitVector.ofNat 32
        (Silean.BitVector.toNat 32 left + Silean.BitVector.toNat 32 right) by rfl]
    exact Silean.BitVector.toNat_ofNat 32 _
  rw [outputToNat]
  cases carry : (Silean.Modules.Add.addBits 32 left right false).2
  · simp only [carry, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at numeric
    rw [← numeric, Nat.mod_eq_of_lt resultBound]
  · simp only [carry, Bool.toNat_true, Nat.mul_one] at numeric
    rw [← numeric, Nat.add_mod, Nat.mod_eq_of_lt resultBound, Nat.mod_self,
      Nat.add_zero]
    rw [Nat.mod_eq_of_lt resultBound]

end PicoRV.Datapath.ProofSupport
