import Silean.Modules.CarrySaveLayer.CarrySaveLayer

namespace SileanTests.CarrySaveLayerContract

open Silean
open Silean.Modules.CarrySaveLayer

def bits (width value : Nat) : Fin width → Bool :=
  BitVector.ofNat width value

def threeOperands (width first second third : Nat) : Fin 3 → Fin width → Bool
  | 0 => bits width first
  | 1 => bits width second
  | 2 => bits width third

def twoReduced (width first second : Nat) :
    Fin (reducedCount 3) → Fin width → Bool :=
  fun index => if index.val = 0 then bits width first else bits width second

example : reducedCount 0 = 0 := rfl
example : reducedCount 1 = 1 := rfl
example : reducedCount 2 = 2 := rfl
example : reducedCount 3 = 2 := rfl
example : reducedCount 8 = 6 := rfl

example : Accepts 4 3 (threeOperands 4 9 6 7) (twoReduced 4 8 14) := by
  constructor
  · simp only [PreservesTotal]
    native_decide
  · trivial

example : Accepts 4 3 (threeOperands 4 9 6 7) (twoReduced 4 0 6) := by
  constructor
  · simp only [PreservesTotal]
    native_decide
  · trivial

example : ¬Accepts 4 3 (threeOperands 4 9 6 7) (twoReduced 4 0 5) := by
  intro accepted
  have notPreserved :
      ¬PreservesTotal 4 3 (threeOperands 4 9 6 7) (twoReduced 4 0 5) := by
    simp only [PreservesTotal]
    native_decide
  exact notPreserved accepted.1

end SileanTests.CarrySaveLayerContract
