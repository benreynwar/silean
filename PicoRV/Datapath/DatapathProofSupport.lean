import PicoRV.Datapath.DatapathBasicUpdates
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterDerived

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

theorem addResult_eq_addWords (left right : Word) :
    Silean.Modules.AddWithCarry.resultValue 32 left right false =
      addWords left right := by
  funext index
  simp only [Silean.Modules.AddWithCarry.resultValue,
    Silean.Modules.AddWithCarry.totalValue, addWords, wordOfNat,
    Silean.BitVector.ofNat, Bool.toNat_false, Nat.add_zero]

end PicoRV.Datapath.ProofSupport
