import HTFFT.Silean.PipelinedFixedButterfly.PipelinedFixedButterfly
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector

/-! # One physical lane of a rolled FFT stage

This module owns the two feedback delay lines, commutator muxes, one twiddle
ROM port, and one pipelined fixed-point butterfly.  Phase generation and frame
alignment are shared by the parent `FFTStage`.
-/

namespace HTFFT.Silean.FFTStageLane

open _root_.Silean
open HTFFT.FixedPoint

abbrev dataSignalType (dataFormat : Format) : SignalType :=
  .vector (dataFormat.width + dataFormat.width) .bit

abbrev twiddleSignalType (twiddleFormat : Format) : SignalType :=
  .vector (twiddleFormat.width + twiddleFormat.width) .bit

abbrev outputSignalType (dataFormat : Format) : SignalType :=
  let width := PipelinedFixedButterfly.outputComponentWidth dataFormat
  .vector (width + width) .bit

module_ports ports (dataFormat : Format) (twiddleFormat : Format)
    (phaseWidth : Nat) where
  input i_firstHalf : .bit,
  input i_outputPhase : .vector phaseWidth .bit,
  input i_branchA : dataSignalType dataFormat,
  input i_branchB : dataSignalType dataFormat,
  output o_upper : outputSignalType dataFormat,
  output o_lower : outputSignalType dataFormat

end HTFFT.Silean.FFTStageLane
