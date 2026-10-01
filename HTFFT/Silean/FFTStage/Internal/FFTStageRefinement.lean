import HTFFT.Silean.FFTStage.Internal.FFTStageStep
import HTFFT.Silean.FFTStageControl.FFTStageControlDerived
import HTFFT.Silean.FFTStageLane.FFTStageLaneDerived
import HTFFT.Fixed.ButterflyCorrectness

/-! Refinement of the concrete stage children to the pure commutator bank. -/

namespace HTFFT.Silean.FFTStage.Internal

open _root_.Silean
open _root_.Silean.Modules

/-- Combine the shared controller state with one lane's two abstract data
delay states.  The controller's dummy `PUnit` data paths are intentionally
discarded. -/
def mergeState (geometry : Geometry depth)
    (control : FFTStageControl.State (phaseExponent geometry))
    (first second : DelayLine.State geometry.pairDelay α) :
    Commutator.State geometry.pairDelay α :=
  { phase := control.phase
    outputPhase := control.outputPhase
    markerDelay := control.markerDelay
    firstDelay := first
    secondDelay := second }

/-- Pure commutator input represented by one parent cycle and physical lane. -/
def laneBankInput (geometry : Geometry depth)
    (input : (FFTStage.ports configuration geometry).inputs.Values)
    (lane : Fin (butterflyCount geometry)) : Commutator.Input
      ((dataSignalType configuration geometry).Denote) :=
  { first := input .i_first
    a := input .i_data
      (geometry.inputBoundary.laneEquiv.symm (0, lane))
    b := input .i_data
      (geometry.inputBoundary.laneEquiv.symm (1, lane)) }

/-- Project a pure commutator observation to the natural invocation consumed
by one concrete lane's pipelined butterfly. -/
def invocationOfSignal (geometry : Geometry depth)
    (visible : Commutator.Signals geometry.pairDelay
      ((dataSignalType configuration geometry).Denote)) :
    FFTStageLane.Invocation (phaseWidth geometry)
      (dataFormat configuration geometry) :=
  { outputPhase := Fin.cast
      ((Geometry.localPeriod_eq_commutatorPeriod geometry).symm.trans
        (localPeriod_eq_phaseCardinality geometry))
      visible.outputPhase
    operands := visible.operands }

/-- The lane ROM's low-lane/high-phase concatenation denotes exactly the
twiddle offset used by the pure commutator schedule. -/
theorem laneTwiddleAddress_val
    (geometry : Geometry depth)
    (phase : Fin (2 * geometry.pairDelay))
    (lane : Fin (butterflyCount geometry)) :
    (FFTStageLane.twiddleAddress (phaseWidth geometry)
      (laneAddressWidth geometry) lane.val
      (Fin.cast
        ((Geometry.localPeriod_eq_commutatorPeriod geometry).symm.trans
          (localPeriod_eq_phaseCardinality geometry)) phase)).val =
      (twiddleAddress geometry phase lane).val := by
  unfold FFTStageLane.twiddleAddress
  rw [BitVector.toIndex_val, VectorConcat.toNat_concat,
    BitVector.toNat_ofNat, BitVector.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.mod_eq_of_lt]
    · change lane.val +
          BitVector.cardinality (laneAddressWidth geometry) * phase.val =
        lane.val + geometry.outputBoundary.lanesPerBranch * phase.val
      congr 2
      simp [laneAddressWidth, BoundaryGeometry.lanesPerBranch,
        Geometry.outputBoundary, BitVector.cardinality_eq_pow]
    · exact (Fin.cast
        ((Geometry.localPeriod_eq_commutatorPeriod geometry).symm.trans
          (localPeriod_eq_phaseCardinality geometry)) phase).isLt
  · simpa only [← butterflyCount_eq_laneCardinality] using lane.isLt

/-- Decoding the concrete lane ROM entry recovers the pure schedule's
integer twiddle exactly. -/
theorem decode_laneTwiddleValue
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (twiddleFits : configuration.TwiddlesFit table)
    (visible : Commutator.Signals geometry.pairDelay
      ((dataSignalType configuration geometry).Denote))
    (lane : Fin (butterflyCount geometry)) :
    PipelinedFixedButterfly.decodeComplex
        (configuration.twiddleFormat geometry.stage).width
        (twiddleValues configuration table geometry
          (FFTStageLane.twiddleAddress (phaseWidth geometry)
            (laneAddressWidth geometry) lane.val
            (invocationOfSignal (configuration := configuration)
              geometry visible).outputPhase)) =
      table.value geometry.stage
        (twiddleAddress geometry visible.outputPhase lane) := by
  have addressEqual :
      Fin.cast (by
        rw [show laneAddressWidth geometry + phaseWidth geometry =
          geometry.stage.val from addressWidth_eq geometry]
        exact BitVector.cardinality_eq_pow geometry.stage.val)
        (FFTStageLane.twiddleAddress (phaseWidth geometry)
          (laneAddressWidth geometry) lane.val
          (invocationOfSignal (configuration := configuration)
            geometry visible).outputPhase) =
      twiddleAddress geometry visible.outputPhase lane := by
    apply Fin.ext
    exact laneTwiddleAddress_val geometry visible.outputPhase lane
  unfold twiddleValues
  rw [addressEqual, PipelinedFixedButterfly.decodeComplex_encodeComplex]
  simpa [HTFFT.Butterfly.Fixed.wrapComplex] using
    (HTFFT.Butterfly.Fixed.wrapComplex_eq_of_fits
      (twiddleFits geometry.stage
        (twiddleAddress geometry visible.outputPhase lane)))

/-- The natural result function of a concrete lane, evaluated on a refined
commutator observation, is the pure fixed-point butterfly assigned to that
observation. -/
theorem laneResultValue_eq
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (twiddleFits : configuration.TwiddlesFit table)
    (visible : Commutator.Signals geometry.pairDelay
      ((dataSignalType configuration geometry).Denote))
    (lane : Fin (butterflyCount geometry)) :
    FFTStageLane.resultValue
        (dataFormat configuration geometry)
        (configuration.twiddleFormat geometry.stage)
        (phaseWidth geometry) (laneAddressWidth geometry) lane.val
        (twiddleValues configuration table geometry)
        (invocationOfSignal (configuration := configuration)
          geometry visible) =
      HTFFT.Butterfly.Fixed.butterfly
        (configuration.fixedConfig.butterfly geometry.stage)
        (PipelinedFixedButterfly.decodeComplex
          (dataFormat configuration geometry).width visible.operands.a)
        (PipelinedFixedButterfly.decodeComplex
          (dataFormat configuration geometry).width visible.operands.b)
        (table.value geometry.stage
          (twiddleAddress geometry visible.outputPhase lane)) := by
  unfold FFTStageLane.resultValue PipelinedFixedButterfly.resultValue
  rw [decode_laneTwiddleValue configuration table geometry twiddleFits
    visible lane]
  rw [configuration.butterfly_eq_fixedConfig]
  rfl

private abbrev stageStructure
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String) :=
  FFTStage.moduleStructure depth configuration table geometry pipeline
    twiddleDefinitionName

/-- The abstract delay states and exact butterfly relation extracted from one
physical lane.  This packages the witnesses needed by the parent refinement
without exposing the lane's physical register representation. -/
structure LaneEvidence
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String)
    (hierarchy : List (HierStep (stageStructure configuration table geometry
      pipeline twiddleDefinitionName)))
    (lane : Fin (butterflyCount geometry)) where
  firstInitial :
    DelayLine.State geometry.pairDelay
      ((dataSignalType configuration geometry).Denote)
  firstFinal :
    DelayLine.State geometry.pairDelay
      ((dataSignalType configuration geometry).Denote)
  secondInitial :
    DelayLine.State geometry.pairDelay
      ((dataSignalType configuration geometry).Denote)
  secondFinal :
    DelayLine.State geometry.pairDelay
      ((dataSignalType configuration geometry).Denote)
  firstOutputs :
    List ((dataSignalType configuration geometry).Denote)
  secondOutputs :
    List ((dataSignalType configuration geometry).Denote)
  firstTrace : Trace (DelayLine.Step geometry.pairDelay) firstInitial
    ((hierarchy.map fun step => (step.children (.lane lane)).inputs).map
      (FFTStageLane.firstDelayInput
        (dataFormat configuration geometry)
        (configuration.twiddleFormat geometry.stage)
        (phaseWidth geometry))) firstOutputs firstFinal
  secondTrace : Trace (DelayLine.Step geometry.pairDelay) secondInitial
    (FFTStageLane.secondDelayInputs
      (dataFormat configuration geometry)
      (configuration.twiddleFormat geometry.stage)
      (phaseWidth geometry)
      (hierarchy.map fun step => (step.children (.lane lane)).inputs)
      secondOutputs) secondOutputs secondFinal
  firstLength : firstOutputs.length =
    (hierarchy.map fun step => (step.children (.lane lane)).inputs).length
  secondLength : secondOutputs.length =
    (hierarchy.map fun step => (step.children (.lane lane)).inputs).length
  outputRelation : FixedLatency.Relates pipeline.latency
    (FFTStageLane.outputRelation
      (dataFormat configuration geometry)
      (configuration.twiddleFormat geometry.stage)
      (phaseWidth geometry) (laneAddressWidth geometry) lane.val
      (twiddleValues configuration table geometry))
    (FFTStageLane.invocationsOf
      (dataFormat configuration geometry)
      (configuration.twiddleFormat geometry.stage)
      (phaseWidth geometry)
      (hierarchy.map fun step => (step.children (.lane lane)).inputs)
      firstOutputs secondOutputs)
    (hierarchy.map fun step => (step.children (.lane lane)).outputs)

/-- Synchronized controller and lane-delay traces are exactly one lane of
the executable pure commutator.  This is the central stateful refinement
lemma; the exposed result is the state-free invocation sequence. -/
theorem laneInvocations_eq_runDetailed
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String)
    (lane : Fin (butterflyCount geometry))
    (hierarchy : List (HierStep (stageStructure configuration table geometry
      pipeline twiddleDefinitionName)))
    (solutions : ∀ step ∈ hierarchy,
      (stageStructure configuration table geometry pipeline
        twiddleDefinitionName).IsSolution step)
    (controlInitial controlFinal :
      FFTStageControl.State (phaseExponent geometry))
    (controlTrace : Trace
      (FFTStageControl.Transition (phaseExponent geometry)) controlInitial
      (hierarchy.map fun step => (step.children .control).inputs)
      (hierarchy.map fun step => (step.children .control).outputs)
      controlFinal)
    (firstInitial firstFinal secondInitial secondFinal :
      DelayLine.State geometry.pairDelay
        ((dataSignalType configuration geometry).Denote))
    (firstOutputs secondOutputs : List
      ((dataSignalType configuration geometry).Denote))
    (firstTrace : Trace (DelayLine.Step geometry.pairDelay) firstInitial
      ((hierarchy.map fun step => (step.children (.lane lane)).inputs).map
        (FFTStageLane.firstDelayInput
          (dataFormat configuration geometry)
          (configuration.twiddleFormat geometry.stage)
          (phaseWidth geometry))) firstOutputs firstFinal)
    (secondTrace : Trace (DelayLine.Step geometry.pairDelay) secondInitial
      (FFTStageLane.secondDelayInputs
        (dataFormat configuration geometry)
        (configuration.twiddleFormat geometry.stage)
        (phaseWidth geometry)
        (hierarchy.map fun step => (step.children (.lane lane)).inputs)
        secondOutputs) secondOutputs secondFinal)
    (firstLength : firstOutputs.length = hierarchy.length)
    (secondLength : secondOutputs.length = hierarchy.length) :
    ((Commutator.runDetailed geometry.pairDelay
        (Geometry.pairDelay_pos geometry)
        (mergeState geometry controlInitial firstInitial secondInitial)
        (hierarchy.map fun step => laneBankInput geometry step.inputs lane)).1.map
      (invocationOfSignal (configuration := configuration) geometry)) =
      FFTStageLane.invocationsOf
        (dataFormat configuration geometry)
        (configuration.twiddleFormat geometry.stage)
        (phaseWidth geometry)
        (hierarchy.map fun step => (step.children (.lane lane)).inputs)
        firstOutputs secondOutputs := by
  induction hierarchy generalizing controlInitial firstInitial secondInitial
      firstOutputs secondOutputs with
  | nil =>
      cases controlTrace
      cases firstTrace
      cases secondTrace
      rfl
  | cons step hierarchy induction =>
      cases controlTrace with
      | @cons _ controlNextState _ _ _ _ _ controlStep controlRest =>
        cases firstTrace with
        | @cons _ firstNextState _ _ _ _ firstOutput firstStep firstRest =>
          cases secondOutputs with
          | nil => simp at secondLength
          | cons secondOutput secondOutputs =>
            cases secondTrace with
            | @cons _ secondNextState _ _ _ _ _ secondStep secondRest =>
            have solution := solutions step (by simp)
            have laneInputs := laneInputs_of_solution solution lane
            have controlInput := controlInput_of_solution solution
            have controlMatches := controlStep.1
            have controlNext := controlStep.2
            have firstOutputEq := firstStep.1
            have secondOutputEq := secondStep.1
            have firstNext := firstStep.2
            have secondNext := secondStep.2
            let fullVisible := Commutator.signals geometry.pairDelay
              (Geometry.pairDelay_pos geometry)
              (mergeState geometry controlInitial firstInitial secondInitial)
              (laneBankInput geometry step.inputs lane)
            let controlVisible := Commutator.signals geometry.pairDelay
              (Geometry.pairDelay_pos geometry) controlInitial
              (FFTStageControl.inputValue (phaseExponent geometry)
                (step.children .control).inputs)
            change controlNextState =
              Commutator.nextState geometry.pairDelay
                (Geometry.pairDelay_pos geometry) controlInitial
                (FFTStageControl.inputValue (phaseExponent geometry)
                  (step.children .control).inputs) at controlNext
            have firstOutputEq' : firstOutput =
                DelayLine.output geometry.pairDelay
                  (Geometry.pairDelay_pos geometry) firstInitial := by
              rw [firstOutputEq]
              simp [DelayLine.output]
            have secondOutputEq' : secondOutput =
                DelayLine.output geometry.pairDelay
                  (Geometry.pairDelay_pos geometry) secondInitial := by
              rw [secondOutputEq]
              simp [DelayLine.output]
            have controlFirstHalfEq :
                controlVisible.firstHalf = fullVisible.firstHalf := by
              simp [controlVisible, fullVisible, Commutator.signals,
                mergeState, laneBankInput, FFTStageControl.inputValue,
                controlInput]
            have controlOutputPhaseEq :
                controlVisible.outputPhase = fullVisible.outputPhase := by
              simp [controlVisible, fullVisible, Commutator.signals,
                mergeState, laneBankInput, FFTStageControl.inputValue,
                controlInput]
            have controlDelayedFirstEq :
                controlVisible.delayedFirst = fullVisible.delayedFirst := by
              simp [controlVisible, fullVisible, Commutator.signals,
                mergeState, laneBankInput, FFTStageControl.inputValue,
                controlInput]
            have firstHalfEq :
                (step.children (.lane lane)).inputs .i_firstHalf =
                  fullVisible.firstHalf :=
              laneInputs.1.trans
                (controlMatches.2.1.trans controlFirstHalfEq)
            have outputPhaseEq :
                (step.children (.lane lane)).inputs .i_outputPhase =
                  BitVector.ofNat (phaseWidth geometry)
                    fullVisible.outputPhase.val := by
              have equal := laneInputs.2.1.trans
                (controlMatches.2.2.trans
                  (congrArg (FFTStageControl.phaseBits
                    (phaseExponent geometry)) controlOutputPhaseEq))
              simpa [FFTStageControl.phaseBits, phaseWidth,
                FFTStageControl.Internal.phaseWidth, phaseExponent] using equal
            have headEqual :
                invocationOfSignal (configuration := configuration) geometry
                    (Commutator.signals geometry.pairDelay
                      (Geometry.pairDelay_pos geometry)
                      (mergeState geometry controlInitial firstInitial
                        secondInitial)
                      (laneBankInput geometry step.inputs lane)) =
                  FFTStageLane.invocationValue
                    (dataFormat configuration geometry)
                    (configuration.twiddleFormat geometry.stage)
                    (phaseWidth geometry)
                    ((step.children (.lane lane)).inputs)
                    firstOutput secondOutput := by
              rw [FFTStageLane.Invocation.mk.injEq]
              constructor
              · apply Fin.ext
                unfold invocationOfSignal FFTStageLane.invocationValue
                  FFTStageLane.inputPhase
                dsimp only
                rw [outputPhaseEq]
                change fullVisible.outputPhase.val =
                  (BitVector.toIndex (phaseWidth geometry)
                    (BitVector.ofNat (phaseWidth geometry)
                      fullVisible.outputPhase.val)).val
                rw [BitVector.toIndex_val, BitVector.toNat_ofNat,
                  Nat.mod_eq_of_lt (by
                  rw [← localPeriod_eq_phaseCardinality]
                  rw [Geometry.localPeriod_eq_commutatorPeriod]
                  exact fullVisible.outputPhase.isLt)]
              · unfold invocationOfSignal FFTStageLane.invocationValue
                change fullVisible.operands =
                  bif (step.children (.lane lane)).inputs .i_firstHalf then
                    Commutator.Operands.mk secondOutput firstOutput
                  else
                    Commutator.Operands.mk firstOutput
                      ((step.children (.lane lane)).inputs .i_branchA)
                rw [firstHalfEq, laneInputs.2.2.1]
                rw [firstOutputEq', secondOutputEq']
                change (if fullVisible.firstHalf then
                    Commutator.Operands.mk
                      (DelayLine.output geometry.pairDelay
                        (Geometry.pairDelay_pos geometry) secondInitial)
                      (DelayLine.output geometry.pairDelay
                        (Geometry.pairDelay_pos geometry) firstInitial)
                  else
                    Commutator.Operands.mk
                      (DelayLine.output geometry.pairDelay
                        (Geometry.pairDelay_pos geometry) firstInitial)
                      (step.inputs .i_data
                        (geometry.inputBoundary.laneEquiv.symm (0, lane)))) = _
                cases fullVisible.firstHalf <;> simp
            have firstInputEq :
                FFTStageLane.firstDelayInput
                    (dataFormat configuration geometry)
                    (configuration.twiddleFormat geometry.stage)
                    (phaseWidth geometry)
                    ((step.children (.lane lane)).inputs) =
                  fullVisible.firstInput := by
              unfold FFTStageLane.firstDelayInput
              rw [firstHalfEq, laneInputs.2.2.1, laneInputs.2.2.2]
              change (bif fullVisible.firstHalf then
                  step.inputs .i_data
                    (geometry.inputBoundary.laneEquiv.symm (0, lane))
                else step.inputs .i_data
                    (geometry.inputBoundary.laneEquiv.symm (1, lane))) =
                (if fullVisible.firstHalf then
                  step.inputs .i_data
                    (geometry.inputBoundary.laneEquiv.symm (0, lane))
                else step.inputs .i_data
                    (geometry.inputBoundary.laneEquiv.symm (1, lane)))
              cases fullVisible.firstHalf <;> simp
            have secondInputEq :
                FFTStageLane.secondDelayInput
                    (dataFormat configuration geometry)
                    (configuration.twiddleFormat geometry.stage)
                    (phaseWidth geometry)
                    ((step.children (.lane lane)).inputs) secondOutput =
                  fullVisible.secondInput := by
              unfold FFTStageLane.secondDelayInput
              rw [firstHalfEq, laneInputs.2.2.2, secondOutputEq']
              change (bif fullVisible.firstHalf then
                  step.inputs .i_data
                    (geometry.inputBoundary.laneEquiv.symm (1, lane))
                else DelayLine.output geometry.pairDelay
                    (Geometry.pairDelay_pos geometry) secondInitial) =
                (if fullVisible.firstHalf then
                  step.inputs .i_data
                    (geometry.inputBoundary.laneEquiv.symm (1, lane))
                else DelayLine.output geometry.pairDelay
                    (Geometry.pairDelay_pos geometry) secondInitial)
              cases fullVisible.firstHalf <;> simp
            have firstStateEq :
                firstNextState = DelayLine.next geometry.pairDelay
                  fullVisible.firstInput
                  firstInitial := by
              apply funext
              intro index
              rw [firstNext]
              unfold DelayLine.next
              rw [← firstInputEq]
            have secondStateEq :
                secondNextState = DelayLine.next geometry.pairDelay
                  fullVisible.secondInput
                  secondInitial := by
              apply funext
              intro index
              rw [secondNext]
              unfold DelayLine.next
              rw [← secondInputEq]
            have nextStateEq :
                Commutator.nextState geometry.pairDelay
                    (Geometry.pairDelay_pos geometry)
                    (mergeState geometry controlInitial firstInitial
                      secondInitial)
                    (laneBankInput geometry step.inputs lane) =
                  mergeState geometry controlNextState firstNextState
                    secondNextState := by
              have phaseNext := congrArg Commutator.State.phase controlNext
              have outputPhaseNext :=
                congrArg Commutator.State.outputPhase controlNext
              have markerNext := congrArg Commutator.State.markerDelay controlNext
              change controlNextState.outputPhase =
                Commutator.nextPhase geometry.pairDelay
                  (Geometry.pairDelay_pos geometry) controlInitial.outputPhase
                  controlVisible.delayedFirst at outputPhaseNext
              rw [controlDelayedFirstEq] at outputPhaseNext
              simp only [Commutator.nextState, mergeState]
              rw [Commutator.State.mk.injEq]
              refine ⟨?_, ?_, ?_, firstStateEq.symm, secondStateEq.symm⟩
              · simpa [fullVisible, controlVisible, Commutator.nextState,
                  mergeState, laneBankInput, FFTStageControl.inputValue,
                  FFTStageControl.pairDelay, phaseExponent,
                  Geometry.pairDelay, controlInput] using phaseNext.symm
              · exact outputPhaseNext.symm
              · simpa [fullVisible, controlVisible, Commutator.nextState,
                  mergeState, laneBankInput, FFTStageControl.inputValue,
                  FFTStageControl.pairDelay, phaseExponent,
                  Geometry.pairDelay, controlInput] using markerNext.symm
            simp only [Commutator.runDetailed, List.map_cons,
              FFTStageLane.invocationsOf]
            rw [headEqual]
            congr 1
            rw [nextStateEq]
            apply induction
            · intro later member
              exact solutions later (by simp [member])
            · exact controlRest
            · exact firstRest
            · exact secondRest
            · simpa using firstLength
            · simpa using secondLength

/-- At every available butterfly-output cycle, a physical lane's output is
related to the corresponding observation of the refined pure commutator. -/
theorem laneOutputRelation_at
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String)
    (lane : Fin (butterflyCount geometry))
    (hierarchy : List (HierStep (stageStructure configuration table geometry
      pipeline twiddleDefinitionName)))
    (solutions : ∀ step ∈ hierarchy,
      (stageStructure configuration table geometry pipeline
        twiddleDefinitionName).IsSolution step)
    (controlInitial controlFinal :
      FFTStageControl.State (phaseExponent geometry))
    (controlTrace : Trace
      (FFTStageControl.Transition (phaseExponent geometry)) controlInitial
      (hierarchy.map fun step => (step.children .control).inputs)
      (hierarchy.map fun step => (step.children .control).outputs)
      controlFinal)
    (evidence : LaneEvidence configuration table geometry pipeline
      twiddleDefinitionName hierarchy lane)
    (t : Nat) (sourceInTrace : t < hierarchy.length)
    (outputInTrace : t + pipeline.latency < hierarchy.length) :
    FFTStageLane.outputRelation
      (dataFormat configuration geometry)
      (configuration.twiddleFormat geometry.stage)
      (phaseWidth geometry) (laneAddressWidth geometry) lane.val
      (twiddleValues configuration table geometry)
      (invocationOfSignal (configuration := configuration) geometry
        (Commutator.visibleAt geometry.pairDelay
          (Geometry.pairDelay_pos geometry)
          (mergeState geometry controlInitial evidence.firstInitial
            evidence.secondInitial)
          (hierarchy.map fun step => laneBankInput geometry step.inputs lane)
          t (by simpa using sourceInTrace)))
      ((hierarchy.get ⟨t + pipeline.latency, outputInTrace⟩).children
        (.lane lane)).outputs := by
  have invocationsEqual := laneInvocations_eq_runDetailed configuration table
    geometry pipeline twiddleDefinitionName lane hierarchy solutions
    controlInitial controlFinal controlTrace evidence.firstInitial
    evidence.firstFinal evidence.secondInitial evidence.secondFinal
    evidence.firstOutputs evidence.secondOutputs evidence.firstTrace
    evidence.secondTrace (by simpa using evidence.firstLength)
    (by simpa using evidence.secondLength)
  have refinedRelation := FixedLatency.relates_congr_inputs
    invocationsEqual.symm evidence.outputRelation
  have related := FixedLatency.relation_at refinedRelation t (by
    simpa using outputInTrace)
  simpa only [Commutator.visibleAt, List.get_eq_getElem,
    List.getElem_map] using related

end HTFFT.Silean.FFTStage.Internal
