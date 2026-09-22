import Silean.Modules.SignedRoundShift.SignedRoundShift

namespace SileanTests.SignedRoundShiftContract

open Silean
open Silean.Modules.SignedRoundShift

private def evaluate (retainedWidth discardedWidth : Nat) (value : Int) :
    BitVec retainedWidth :=
  BitVector.toBitVec retainedWidth <|
    resultValue retainedWidth discardedWidth <|
      BitVector.ofBitVec <|
        BitVec.ofInt (discardedWidth + retainedWidth) value

#guard evaluate 4 0 5 == BitVec.ofInt 4 5
#guard evaluate 4 4 23 == BitVec.ofInt 4 1
#guard evaluate 4 4 24 == BitVec.ofInt 4 2
#guard evaluate 4 4 40 == BitVec.ofInt 4 2
#guard evaluate 4 4 (-24) == BitVec.ofInt 4 (-2)
#guard evaluate 4 4 (-8) == BitVec.ofInt 4 0
#guard evaluate 4 4 (-9) == BitVec.ofInt 4 (-1)
#guard evaluate 0 4 7 == BitVec.ofInt 0 0

end SileanTests.SignedRoundShiftContract
