import HTFFT.Silean.PipelinedFixedButterfly.PipelinedFixedButterfly

assert_not_imported HTFFT.Silean.PipelinedFixedButterfly.Internal.PipelinedFixedButterflyStructure
assert_not_imported HTFFT.Silean.PipelinedFixedButterfly.Internal.PipelinedFixedButterflyVerification

namespace HTFFTTests.PipelinedFixedButterflyContract

open Silean
open HTFFT
open HTFFT.FixedPoint
open HTFFT.Silean.PipelinedFixedButterfly

private def pipeline (input : Bool) (multiplierLatency : Nat)
    (beforeRounding product output : Bool) : Pipeline :=
  { registerInputs := input
    complexMultiply :=
      { multiplierLatency
        registerBeforeRounding := beforeRounding }
    registerProduct := product
    registerOutputs := output }

private def signedBits (width : Nat) (value : Int) : Fin width → Bool :=
  BitVector.ofBitVec (BitVec.ofInt width value)

private def packed (width : Nat) (real imag : Int) :
    Fin (width + width) → Bool :=
  encodeComplex width ⟨real, imag⟩

def dataFormat : Format := ⟨4, 2⟩
def twiddleFormat : Format := ⟨4, 2⟩

#guard (pipeline false 0 false false false).latency == 0
#guard (pipeline true 0 false false false).latency == 1
#guard (pipeline false 3 true false false).latency == 4
#guard (pipeline true 3 true true true).latency == 7

#guard outputComponentWidth dataFormat == 5
#guard fixedConfig dataFormat twiddleFormat ==
  HTFFT.Butterfly.Fixed.Config.initial 4 2 4 2

-- Packing is imaginary-low and real-high, including signed values.
#guard decodeComplex 4 (packed 4 (-3) 5) == (⟨-3, 5⟩ : Complex Int)
#guard BitVector.toBitVec 4 (lowComponent 4 (packed 4 (-3) 5)) ==
  BitVector.toBitVec 4 (signedBits 4 5)
#guard BitVector.toBitVec 4 (highComponent 4 (packed 4 (-3) 5)) ==
  BitVector.toBitVec 4 (signedBits 4 (-3))

-- One stage keeps the binary point and grows only the high side by one bit.
#guard (resultValue dataFormat twiddleFormat
  (packed 4 4 0) (packed 4 4 0) (packed 4 4 0)).upper ==
    (⟨8, 0⟩ : Complex Int)
#guard decodeComplex 5
  (encodeComplex 5
    (resultValue dataFormat twiddleFormat
      (packed 4 4 0) (packed 4 4 0) (packed 4 4 0)).upper) ==
    (⟨8, 0⟩ : Complex Int)

#check contract

end HTFFTTests.PipelinedFixedButterflyContract
