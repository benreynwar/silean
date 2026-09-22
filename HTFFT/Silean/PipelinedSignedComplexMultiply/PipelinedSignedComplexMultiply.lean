import Silean.Authoring.ModulePorts
import Silean.Modules.Arithmetic
import Silean.Modules.SignedRoundShift.SignedRoundShift
import Silean.Semantics.FixedLatency

/-! # Pipelined rounded signed complex multiplication

`PipelinedSignedComplexMultiply` interprets each input component as a signed
two's-complement integer.  Each real or imaginary numerator is formed at full
precision and rounded only after its two scalar products have been combined.
The public behavior is a trace relation with statically selected latency.

The output drops `discardedWidth` low bits from the full numerator width.  Nat
subtraction deliberately saturates: requesting at least the whole numerator
width gives a zero-width result.  This makes every natural-number parameter
well-defined without a proof argument or a hidden high-bit truncation.
-/

namespace HTFFT.Silean.PipelinedSignedComplexMultiply

open _root_.Silean
open _root_.Silean.Modules

/-- Static placement of the registers inside the complex multiplier.

The scalar products all use the same latency.  When
`registerBeforeRounding` is enabled, both full-width combined numerators are
registered together after the Add/Sub and before either rounder. -/
structure Pipeline where
  multiplierLatency : Nat
  registerBeforeRounding : Bool
deriving DecidableEq, Repr

/-- End-to-end latency selected by a complex-multiplier pipeline. -/
def Pipeline.latency (pipeline : Pipeline) : Nat :=
  pipeline.multiplierLatency + Bool.toNat pipeline.registerBeforeRounding

/-- Width of each exact scalar product. -/
def productWidth (leftWidth rightWidth : Nat) : Nat :=
  leftWidth + rightWidth

/-- Width needed for the exact sum or difference of two signed products. -/
def numeratorWidth (leftWidth rightWidth : Nat) : Nat :=
  Arithmetic.resultWidth (productWidth leftWidth rightWidth)
    (productWidth leftWidth rightWidth) true

/-- Width remaining after discarding low numerator bits. -/
def resultWidth (leftWidth rightWidth discardedWidth : Nat) : Nat :=
  numeratorWidth leftWidth rightWidth - discardedWidth

/-- Interpret one component as an ordinary signed integer. -/
def componentValue (width : Nat) (value : Fin width → Bool) : Int :=
  Arithmetic.operandValue true width value

/-- Exact full-precision real numerator. -/
def realNumerator (leftWidth rightWidth : Nat)
    (leftReal leftImag : Fin leftWidth → Bool)
    (rightReal rightImag : Fin rightWidth → Bool) : Int :=
  componentValue leftWidth leftReal * componentValue rightWidth rightReal -
    componentValue leftWidth leftImag * componentValue rightWidth rightImag

/-- Exact full-precision imaginary numerator. -/
def imagNumerator (leftWidth rightWidth : Nat)
    (leftReal leftImag : Fin leftWidth → Bool)
    (rightReal rightImag : Fin rightWidth → Bool) : Int :=
  componentValue leftWidth leftReal * componentValue rightWidth rightImag +
    componentValue leftWidth leftImag * componentValue rightWidth rightReal

/-- Encode one rounded component at the naturally retained width. -/
def roundedValue (leftWidth rightWidth discardedWidth : Nat)
    (numerator : Int) :
    Fin (resultWidth leftWidth rightWidth discardedWidth) → Bool :=
  Arithmetic.encode (resultWidth leftWidth rightWidth discardedWidth)
    (SignedRoundShift.roundNearestEven discardedWidth numerator)

def realResultValue (leftWidth rightWidth discardedWidth : Nat)
    (leftReal leftImag : Fin leftWidth → Bool)
    (rightReal rightImag : Fin rightWidth → Bool) :
    Fin (resultWidth leftWidth rightWidth discardedWidth) → Bool :=
  roundedValue leftWidth rightWidth discardedWidth
    (realNumerator leftWidth rightWidth leftReal leftImag rightReal rightImag)

def imagResultValue (leftWidth rightWidth discardedWidth : Nat)
    (leftReal leftImag : Fin leftWidth → Bool)
    (rightReal rightImag : Fin rightWidth → Bool) :
    Fin (resultWidth leftWidth rightWidth discardedWidth) → Bool :=
  roundedValue leftWidth rightWidth discardedWidth
    (imagNumerator leftWidth rightWidth leftReal leftImag rightReal rightImag)

module_ports ports (leftWidth : Nat) (rightWidth : Nat)
    (discardedWidth : Nat) where
  input leftReal : .vector leftWidth .bit,
  input leftImag : .vector leftWidth .bit,
  input rightReal : .vector rightWidth .bit,
  input rightImag : .vector rightWidth .bit,
  output resultReal : .vector
    (resultWidth leftWidth rightWidth discardedWidth) .bit,
  output resultImag : .vector
    (resultWidth leftWidth rightWidth discardedWidth) .bit

/-- Every input whose delayed output occurs in the supplied trace produces the
once-rounded exact complex product at that output position. -/
def contract (leftWidth rightWidth discardedWidth : Nat) (pipeline : Pipeline)
    (trace : BoundaryTrace
      (ports leftWidth rightWidth discardedWidth)) : Prop :=
  FixedLatency.Holds pipeline.latency
    (fun
      (input : (ports leftWidth rightWidth discardedWidth).inputs.Values)
      (output : (ports leftWidth rightWidth discardedWidth).outputs.Values) =>
        output .resultReal =
            realResultValue leftWidth rightWidth discardedWidth
              (input .leftReal) (input .leftImag)
              (input .rightReal) (input .rightImag) ∧
          output .resultImag =
            imagResultValue leftWidth rightWidth discardedWidth
              (input .leftReal) (input .leftImag)
              (input .rightReal) (input .rightImag)) trace

end HTFFT.Silean.PipelinedSignedComplexMultiply
