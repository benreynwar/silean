import Silean.Authoring.ModulePorts

/-! # Shared control for one rolled FFT stage -/

namespace HTFFT.Silean.FFTStageControl

open _root_.Silean

module_ports ports (phaseWidth : Nat) where
  input i_first : .bit,
  output o_delayedFirst : .bit,
  output o_firstHalf : .bit,
  output o_outputPhase : .vector phaseWidth .bit

end HTFFT.Silean.FFTStageControl
