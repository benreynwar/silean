namespace Silean2.Foundations

def bitVectorToNat {width : Nat} (bits : Fin width → Bool) : Nat :=
  (List.finRange width).reverse.foldl (fun result i => result * 2 + (bits i).toNat) 0

def natToBitVector {width : Nat} (value : Fin (2 ^ width)) : Fin width → Bool :=
  fun i => value.val.testBit i.val

def three (x : Fin 3) : Bool := match x with
  | 0 => true
  | 1 => true
  | 2 => false

#guard bitVectorToNat three = 3

end Silean2.Foundations
