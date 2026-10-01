import HTFFT.Silean.FFTStageControl.Internal.FFTStageControlVerification

/-! Public placement and correctness declarations for rolled-stage control. -/

namespace HTFFT.Silean.FFTStageControl

open _root_.Silean
open _root_.Silean.Authoring.CircuitDescription

/-- Place the shared phase and frame-marker control for one rolled stage. -/
noncomputable def place (phaseExponent : Nat) (i_first : Net .bit) :
    Builder (ports.OutputNets (Internal.phaseWidth phaseExponent)) :=
  ports.placeIndexed (Internal.phaseWidth phaseExponent) "fft_stage_control"
    (moduleStructure phaseExponent) (naming phaseExponent) i_first

attribute [circuit_description] place

/-- Shared control has a unique structural solution for every input and
physical state. -/
theorem structuralCertification (phaseExponent : Nat) :
    ModuleStructuralCertification (moduleStructure phaseExponent) :=
  Internal.structuralCertification phaseExponent

/-- Every concrete control execution follows the pure commutator control
projection from hidden initial state. -/
theorem contract_of_execution
    (phaseExponent : Nat)
    {initialState finalState : (moduleStructure phaseExponent).State}
    {inputs : List
      (ports (Internal.phaseWidth phaseExponent)).inputs.Values}
    {outputs : List
      (ports (Internal.phaseWidth phaseExponent)).outputs.Values}
    (execution : (moduleStructure phaseExponent).Executes
      initialState inputs outputs finalState) :
    contract phaseExponent execution.toBoundaryTrace :=
  Internal.contract_of_execution phaseExponent execution

end HTFFT.Silean.FFTStageControl
