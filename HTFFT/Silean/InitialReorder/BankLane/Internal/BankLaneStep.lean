import HTFFT.Silean.InitialReorder.BankLane.Internal.BankLaneStructural

/-! One-cycle refinement of a concrete lane memory to its natural read-old
transition. -/

namespace HTFFT.Silean.InitialReorder.BankLane.Internal
open FFT

open _root_.Silean
open _root_.Silean.Modules

private abbrev BankState (configuration : Configuration depth) :=
  (RegisterBank.cycleContract (sampleType configuration)
    (InitialReorder.addressWidth configuration) 1).state.Values

private abbrev OutputState (configuration : Configuration depth) :=
  (Register.cycleContract (sampleType configuration)).state.Values

def logicalState (configuration : Configuration depth)
    (bank : BankState configuration) (output : OutputState configuration) :
    State configuration :=
  { entries := bank .entries
    output := output .stored }

theorem transition_of_solution (depth : Nat)
    (configuration : Configuration depth)
    {step : HierStep (moduleStructure depth configuration)}
    (satisfies : (moduleStructure depth configuration).IsSolution step)
    {bankCurrent bankNext : BankState configuration}
    {outputCurrent outputNext : OutputState configuration}
    (bankAllowed :
      (RegisterBank.cycleContract (sampleType configuration)
        (InitialReorder.addressWidth configuration) 1).Allows {
          inputs := (step.children .bank).inputs
          currentState := bankCurrent
          outputs := (step.children .bank).outputs
          nextState := bankNext })
    (outputAllowed :
      (Register.cycleContract (sampleType configuration)).Allows {
          inputs := (step.children .outputRegister).inputs
          currentState := outputCurrent
          outputs := (step.children .outputRegister).outputs
          nextState := outputNext }) :
    Transition configuration step.inputs
      (logicalState configuration bankCurrent outputCurrent) step.outputs
      (logicalState configuration bankNext outputNext) := by
  have trueRealizes := ModuleStructure.child_realizes satisfies .trueSource
  have unpackRealizes := ModuleStructure.child_realizes satisfies .payloadUnpack
  simp only [structuralChildren] at trueRealizes unpackRealizes
  obtain ⟨_, _, trueAllowed⟩ :=
    Constant.allowed_of_realization .bit true trueRealizes
  have trueValue := Constant.output_of_allowed .bit true trueAllowed
  have unpackValue := NamedTupleSplitter.outputs_of_realization
    (InitialReorder.Lane.payloadMap configuration) unpackRealizes
  have bankRead := RegisterBank.readValue_of_allowed bankAllowed (0 : Fin 1)
  have bankNextValue := RegisterBank.next_entries_of_allowed bankAllowed
  have registerOutput := Register.output_of_allowed outputAllowed
  have registerNext := Register.next_stored_of_allowed outputAllowed
  have unpackInput := ModuleStructure.child_input satisfies .payloadUnpack .value
  have bankEnable := ModuleStructure.child_input satisfies .bank .writeEnable
  have bankWriteAddress :=
    ModuleStructure.child_input satisfies .bank .writeAddress
  have bankWriteValue := ModuleStructure.child_input satisfies .bank .writeValue
  have bankReadAddress :=
    ModuleStructure.child_input satisfies .bank (.readAddress 0)
  have registerInput :=
    ModuleStructure.child_input satisfies .outputRegister .input
  have boundary := ModuleStructure.parent_output satisfies .o_data
  change (step.children .trueSource).outputs .output = true at trueValue
  change (step.children .payloadUnpack).outputs =
    NamedTupleSplitter.splitValue
      (InitialReorder.Lane.payloadMap configuration)
      ((step.children .payloadUnpack).inputs .value) at unpackValue
  change (step.children .bank).outputs (.readValue 0) =
    bankCurrent .entries (BitVector.toIndex
      (InitialReorder.addressWidth configuration)
      ((step.children .bank).inputs (.readAddress 0))) at bankRead
  change bankNext .entries = RegisterBank.nextEntries
    (InitialReorder.addressWidth configuration)
    ((step.children .bank).inputs .writeEnable)
    ((step.children .bank).inputs .writeAddress)
    ((step.children .bank).inputs .writeValue)
    (bankCurrent .entries) at bankNextValue
  change (step.children .outputRegister).outputs .output =
    outputCurrent .stored at registerOutput
  change outputNext .stored =
    (step.children .outputRegister).inputs .input at registerNext
  change (step.children .payloadUnpack).inputs .value =
    step.inputs .i_writePayload at unpackInput
  change (step.children .bank).inputs .writeEnable =
    (step.children .trueSource).outputs .output at bankEnable
  change (step.children .bank).inputs .writeAddress =
    (step.children .payloadUnpack).outputs .address at bankWriteAddress
  change (step.children .bank).inputs .writeValue =
    (step.children .payloadUnpack).outputs .data at bankWriteValue
  change (step.children .bank).inputs (.readAddress 0) =
    step.inputs .i_readAddress at bankReadAddress
  change (step.children .outputRegister).inputs .input =
    (step.children .bank).outputs (.readValue 0) at registerInput
  change step.outputs .o_data =
    (step.children .outputRegister).outputs .output at boundary
  constructor
  · exact boundary.trans registerOutput
  · apply State.ext
    · rw [logicalState, bankNextValue, bankEnable, trueValue,
        bankWriteAddress, bankWriteValue, unpackValue, unpackInput]
      rfl
    · rw [logicalState, registerNext, registerInput, bankRead,
        bankReadAddress]
      rfl

end HTFFT.Silean.InitialReorder.BankLane.Internal
