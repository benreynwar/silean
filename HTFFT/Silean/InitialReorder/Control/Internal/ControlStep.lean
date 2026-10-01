import HTFFT.Silean.InitialReorder.Control.Internal.ControlStructural

/-! One-cycle refinement from the structural controller to its natural state
machine.  Only public child contracts are used. -/

namespace HTFFT.Silean.InitialReorder.Control.Internal

open _root_.Silean
open _root_.Silean.Modules

private abbrev AddressCounterState (addressWidth : Nat) :=
  (EnabledResetCounter.cycleContract addressWidth
    (oneAddress addressWidth)).state.Values

private abbrev OrientationCounterState :=
  (EnabledResetCounter.cycleContract 1
    (orientationValue false)).state.Values

def controlState (addressWidth : Nat)
    (address : AddressCounterState addressWidth)
    (orientation : OrientationCounterState) : State addressWidth :=
  { storedAddress := address .stored
    reversed := orientation .stored 0 }

theorem transition_of_solution (addressWidth : Nat)
    {step : HierStep (moduleStructure addressWidth)}
    (satisfies : (moduleStructure addressWidth).IsSolution step)
    {addressCurrent addressNext : AddressCounterState addressWidth}
    {orientationCurrent orientationNext : OrientationCounterState}
    (addressAllowed :
      (EnabledResetCounter.cycleContract addressWidth
        (oneAddress addressWidth)).Allows {
          inputs := (step.children .addressCounter).inputs
          currentState := addressCurrent
          outputs := (step.children .addressCounter).outputs
          nextState := addressNext })
    (orientationAllowed :
      (EnabledResetCounter.cycleContract 1
        (orientationValue false)).Allows {
          inputs := (step.children .orientationCounter).inputs
          currentState := orientationCurrent
          outputs := (step.children .orientationCounter).outputs
          nextState := orientationNext }) :
    Transition addressWidth step.inputs
      (controlState addressWidth addressCurrent orientationCurrent)
      step.outputs
      (controlState addressWidth addressNext orientationNext) := by
  have trueRealizes := ModuleStructure.child_realizes satisfies .trueSource
  have falseRealizes := ModuleStructure.child_realizes satisfies .falseSource
  have zeroRealizes := ModuleStructure.child_realizes satisfies .zeroAddress
  have lastRealizes := ModuleStructure.child_realizes satisfies .lastAddress
  have muxRealizes := ModuleStructure.child_realizes satisfies .addressSelect
  have equalityRealizes := ModuleStructure.child_realizes satisfies .atLast
  have splitRealizes := ModuleStructure.child_realizes satisfies .orientationSplit
  simp only [structuralChildren] at trueRealizes falseRealizes zeroRealizes
  simp only [structuralChildren] at lastRealizes muxRealizes equalityRealizes
  simp only [structuralChildren] at splitRealizes

  obtain ⟨_, _, trueAllowed⟩ :=
    Constant.allowed_of_realization .bit true trueRealizes
  obtain ⟨_, _, falseAllowed⟩ :=
    Constant.allowed_of_realization .bit false falseRealizes
  obtain ⟨_, _, zeroAllowed⟩ := Constant.allowed_of_realization
    (.vector addressWidth .bit) (zeroAddress addressWidth) zeroRealizes
  obtain ⟨_, _, lastAllowed⟩ := Constant.allowed_of_realization
    (.vector addressWidth .bit) (lastAddress addressWidth) lastRealizes

  have trueOutput := Constant.output_of_allowed .bit true trueAllowed
  have falseOutput := Constant.output_of_allowed .bit false falseAllowed
  have zeroOutput := Constant.output_of_allowed (.vector addressWidth .bit)
    (zeroAddress addressWidth) zeroAllowed
  have lastOutput := Constant.output_of_allowed (.vector addressWidth .bit)
    (lastAddress addressWidth) lastAllowed
  have addressValue := EnabledResetCounter.value_of_allowed addressAllowed
  have orientationValueEq :=
    EnabledResetCounter.value_of_allowed orientationAllowed
  have addressNextEq :=
    EnabledResetCounter.next_stored_of_allowed addressAllowed
  have orientationNextEq :=
    EnabledResetCounter.next_stored_of_allowed orientationAllowed
  have muxOutput := Mux.result_of_realization
    (.vector addressWidth .bit) muxRealizes
  have equalityOutputRaw := Equality.result_of_realization
    (.vector addressWidth .bit) equalityRealizes

  have addressEnable :=
    ModuleStructure.child_input satisfies .addressCounter .enable
  have addressReset :=
    ModuleStructure.child_input satisfies .addressCounter .reset
  have muxSelect :=
    ModuleStructure.child_input satisfies .addressSelect .select
  have muxFalse :=
    ModuleStructure.child_input satisfies .addressSelect .whenFalse
  have muxTrue :=
    ModuleStructure.child_input satisfies .addressSelect .whenTrue
  have equalityLeft := ModuleStructure.child_input satisfies .atLast .left
  have equalityRight := ModuleStructure.child_input satisfies .atLast .right
  have orientationEnable :=
    ModuleStructure.child_input satisfies .orientationCounter .enable
  have orientationReset :=
    ModuleStructure.child_input satisfies .orientationCounter .reset
  have splitInput :=
    ModuleStructure.child_input satisfies .orientationSplit .value
  have addressBoundary := ModuleStructure.parent_output satisfies .o_address
  have orientationBoundary :=
    ModuleStructure.parent_output satisfies .o_reversed

  change (step.children .addressCounter).inputs .enable =
    (step.children .trueSource).outputs .output at addressEnable
  change (step.children .addressCounter).inputs .reset =
    step.inputs .i_first at addressReset
  change (step.children .addressSelect).inputs .select =
    step.inputs .i_first at muxSelect
  change (step.children .addressSelect).inputs .whenFalse =
    (step.children .addressCounter).outputs .value at muxFalse
  change (step.children .addressSelect).inputs .whenTrue =
    (step.children .zeroAddress).outputs .output at muxTrue
  change (step.children .atLast).inputs .left =
    (step.children .addressSelect).outputs .result at equalityLeft
  change (step.children .atLast).inputs .right =
    (step.children .lastAddress).outputs .output at equalityRight
  change (step.children .orientationCounter).inputs .enable =
    (step.children .atLast).outputs .result at orientationEnable
  change (step.children .orientationCounter).inputs .reset =
    (step.children .falseSource).outputs .output at orientationReset
  change (step.children .orientationSplit).inputs .value =
    (step.children .orientationCounter).outputs .value at splitInput
  change step.outputs .o_address =
    (step.children .addressSelect).outputs .result at addressBoundary
  change step.outputs .o_reversed =
    (step.children .orientationSplit).outputs 0 at orientationBoundary

  change (step.children .trueSource).outputs .output = true at trueOutput
  change (step.children .falseSource).outputs .output = false at falseOutput
  change (step.children .zeroAddress).outputs .output =
    zeroAddress addressWidth at zeroOutput
  change (step.children .lastAddress).outputs .output =
    lastAddress addressWidth at lastOutput
  change (step.children .addressCounter).outputs .value =
    addressCurrent .stored at addressValue
  change (step.children .orientationCounter).outputs .value =
    orientationCurrent .stored at orientationValueEq
  change (step.children .addressSelect).outputs .result =
    bif (step.children .addressSelect).inputs .select then
      (step.children .addressSelect).inputs .whenTrue
    else (step.children .addressSelect).inputs .whenFalse at muxOutput
  change (step.children .atLast).outputs .result =
    (SignalType.vector addressWidth .bit).equal
      ((step.children .atLast).inputs .left)
      ((step.children .atLast).inputs .right) at equalityOutputRaw

  have effectiveOutput :
      (step.children .addressSelect).outputs .result =
        effectiveAddress addressWidth (step.inputs .i_first)
          (controlState addressWidth addressCurrent orientationCurrent) := by
    rw [muxOutput, muxSelect, muxFalse, muxTrue, zeroOutput, addressValue]
    rfl

  have equalityInputs :
      (step.children .atLast).inputs .left =
          (step.children .addressSelect).outputs .result ∧
        (step.children .atLast).inputs .right =
          (step.children .lastAddress).outputs .output :=
    ⟨equalityLeft, equalityRight⟩
  have equalityOutput :
      (step.children .atLast).outputs .result =
        atLastAddress addressWidth
          (effectiveAddress addressWidth (step.inputs .i_first)
            (controlState addressWidth addressCurrent orientationCurrent)) := by
    apply Bool.eq_iff_iff.mpr
    rw [atLastAddress_eq_true_iff]
    rw [equalityOutputRaw]
    rw [SignalType.equal_eq_true_iff]
    rw [equalityInputs.1, equalityInputs.2, effectiveOutput, lastOutput]
    rfl

  have splitOutputs :
      (step.children .orientationSplit).outputs =
        orientationSplitter.outputValues
          (step.children .orientationSplit).inputs := by
    let certification := orientationSplitter.certified.certification
    obtain ⟨current, corresponds⟩ := certification.hasCorrespondingState
      (step.children .orientationSplit).currentState
    obtain ⟨_, allowed, _⟩ := certification.allows_of_realizes current
      (step.children .orientationSplit).step corresponds splitRealizes
    exact (Composition.SignalSplitter.outputRule_holds_iff
      orientationSplitter _ _ _).mp (allowed.1 .apply)
  have orientationOutput :
      (step.children .orientationSplit).outputs 0 =
        orientationCurrent .stored 0 := by
    have component := congrFun splitOutputs (0 : Fin 1)
    simpa [orientationSplitter, Composition.SignalSplitter.outputValues,
      splitInput, orientationValueEq] using component

  have addressNextValue :
      addressNext .stored =
        _root_.Silean.Modules.Increment.incrementValue addressWidth
          (effectiveAddress addressWidth (step.inputs .i_first)
            (controlState addressWidth addressCurrent orientationCurrent)) := by
    change addressNext .stored = EnabledResetCounter.nextValue addressWidth
      (oneAddress addressWidth)
      ((step.children .addressCounter).inputs .enable)
      ((step.children .addressCounter).inputs .reset)
      (addressCurrent .stored) at addressNextEq
    rw [addressNextEq, addressEnable, addressReset, trueOutput]
    cases first : step.inputs .i_first <;>
      simp [EnabledResetCounter.nextValue, effectiveAddress, controlState]

  have orientationNextValue :
      orientationNext .stored 0 =
        bif atLastAddress addressWidth
            (effectiveAddress addressWidth (step.inputs .i_first)
              (controlState addressWidth addressCurrent orientationCurrent))
          then !orientationCurrent .stored 0
          else orientationCurrent .stored 0 := by
    change orientationNext .stored = EnabledResetCounter.nextValue 1
      (orientationValue false)
      ((step.children .orientationCounter).inputs .enable)
      ((step.children .orientationCounter).inputs .reset)
      (orientationCurrent .stored) at orientationNextEq
    have enable : (step.children .orientationCounter).inputs .enable =
        atLastAddress addressWidth
          (effectiveAddress addressWidth (step.inputs .i_first)
            (controlState addressWidth addressCurrent orientationCurrent)) :=
      orientationEnable.trans equalityOutput
    have reset : (step.children .orientationCounter).inputs .reset = false :=
      orientationReset.trans falseOutput
    rw [orientationNextEq, enable, reset]
    cases last : atLastAddress addressWidth
        (effectiveAddress addressWidth (step.inputs .i_first)
          (controlState addressWidth addressCurrent orientationCurrent)) <;>
      simp [EnabledResetCounter.nextValue, increment_orientation_at]

  constructor
  · constructor
    · exact addressBoundary.trans effectiveOutput
    · exact orientationBoundary.trans orientationOutput
  · apply State.ext
    · exact addressNextValue
    · exact orientationNextValue

end HTFFT.Silean.InitialReorder.Control.Internal
