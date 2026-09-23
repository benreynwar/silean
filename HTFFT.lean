import HTFFT.Complex
import HTFFT.FixedPoint
import HTFFT.FixedPoint.Correctness
import HTFFT.FixedPoint.Range
import HTFFT.Butterfly
import HTFFT.Exact.Indexing
import HTFFT.Exact.Radix2
import HTFFT.Exact.DFT
import HTFFT.Exact.Layered
import HTFFT.Exact.LayeredCorrectness
import HTFFT.Fixed.Layered
import HTFFT.Fixed.Error
import HTFFT.Fixed.TwiddleTable
import HTFFT.Fixed.Twiddle8
import HTFFT.Fixed.ButterflyCorrectness
import HTFFT.Fixed.ButterflyRange
import HTFFT.Fixed.LayeredRange
import HTFFT.Fixed.LayeredCorrectness
import HTFFT.Fixed.Twiddle8Accuracy
import HTFFT.Silean.PipelinedSignedComplexMultiply
import HTFFT.Silean.PipelinedFixedButterfly
import HTFFT.Silean.FFTConfiguration
import HTFFT.Silean.UnrolledFFTLayer
import HTFFT.Silean.UnrolledFFTNetwork
import HTFFT.Silean.UnrolledFFT
import HTFFT.Silean.FFTStage
import HTFFT.Silean.FFT

/-! Specifications, numerical proofs, and project-specific Silean hardware for
the HTFFT project. -/
