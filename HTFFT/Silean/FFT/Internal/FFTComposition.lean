import HTFFT.Silean.FFT.FFT
import HTFFT.Silean.UnrolledFFTNetwork.UnrolledFFTNetwork

/-! Pure composition facts for the top-level FFT data path. -/

namespace HTFFT.Silean.FFT.Internal

/-- The initial reorder presents the complete globally bit-reversed vector in
cycle-major order to the unrolled prefix network. -/
@[simp] theorem initialReorder_cycle
    (configuration : Configuration depth)
    (input : InputFrame configuration)
    (cycle : Fin configuration.frameLength)
    (lane : Fin (2 ^ configuration.laneDepth)) :
    InitialReorder.resultFrame configuration input cycle lane =
      HTFFT.Exact.bitReverse (unpackInput configuration input)
        (naturalLayout configuration (cycle, lane)) :=
  rfl

private theorem blockGroup_cardinality
    (configuration : Configuration depth)
    (stage : Fin configuration.laneDepth) :
    configuration.frameLength *
        2 ^ (configuration.laneDepth - stage.val - 1) =
      2 ^ (depth - (configuration.globalStage stage).val - 1) := by
  rw [Configuration.frameLength, ← Nat.pow_add]
  congr
  have stageLt := stage.isLt
  have laneLe := configuration.laneDepth_le_depth
  change depth - configuration.laneDepth +
      (configuration.laneDepth - stage.val - 1) =
    depth - stage.val - 1
  omega

private def blockGroupEquiv (configuration : Configuration depth)
    (stage : Fin configuration.laneDepth) :
    Fin configuration.frameLength ×
        Fin (2 ^ (configuration.laneDepth - stage.val - 1)) ≃
      Fin (2 ^ (depth - (configuration.globalStage stage).val - 1)) :=
  finProdFinEquiv.trans (finCongr (blockGroup_cardinality configuration stage))

private def globalPosition (configuration : Configuration depth)
    (stage : Fin configuration.laneDepth)
    (cycle : Fin configuration.frameLength)
    (position : HTFFT.Exact.LayerPosition configuration.laneDepth stage) :
    HTFFT.Exact.LayerPosition depth (configuration.globalStage stage) where
  group := blockGroupEquiv configuration stage (cycle, position.group)
  branch := position.branch
  offset := position.offset

private theorem layerIndex_globalPosition
    (configuration : Configuration depth)
    (stage : Fin configuration.laneDepth)
    (cycle : Fin configuration.frameLength)
    (position : HTFFT.Exact.LayerPosition configuration.laneDepth stage) :
    HTFFT.Exact.layerIndexEquiv depth (configuration.globalStage stage)
        (globalPosition configuration stage cycle position) =
      naturalLayout configuration
        (cycle, HTFFT.Exact.layerIndexEquiv configuration.laneDepth stage
          position) := by
  apply Fin.ext
  simp only [HTFFT.Exact.layerIndexEquiv_val, naturalLayout_val]
  change position.offset.val + 2 ^ stage.val * position.branch.val +
      (2 * 2 ^ stage.val) *
        (position.group.val +
          2 ^ (configuration.laneDepth - stage.val - 1) * cycle.val) =
    (position.offset.val + 2 ^ stage.val * position.branch.val +
      (2 * 2 ^ stage.val) * position.group.val) +
        configuration.laneCount * cycle.val
  rw [Configuration.laneCount]
  have exponent :
      stage.val + 1 + (configuration.laneDepth - stage.val - 1) =
        configuration.laneDepth := by
    have := stage.isLt
    omega
  rw [show 2 * 2 ^ stage.val = 2 ^ (stage.val + 1) by
    rw [Nat.pow_succ']]
  rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, exponent]
  omega

/-- An early global layer acts independently on each cycle-sized lane block. -/
private theorem butterflyLayer_block
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (stage : Fin configuration.laneDepth)
    (input : HTFFT.Fixed.Vector depth)
    (cycle : Fin configuration.frameLength)
    (lane : Fin (2 ^ configuration.laneDepth)) :
    HTFFT.Fixed.butterflyLayer configuration.unrolled.fixedConfig
        (configuration.prefixTable table) stage
        (fun laneIndex : Fin (2 ^ configuration.laneDepth) =>
          input (naturalLayout configuration (cycle, laneIndex))) lane =
      HTFFT.Fixed.butterflyLayer configuration.arithmetic.fixedConfig table
        (configuration.globalStage stage) input
        (naturalLayout configuration (cycle, lane)) := by
  unfold Configuration.laneCount at *
  unfold Configuration.globalStage at *
  obtain ⟨position, rfl⟩ :=
    (HTFFT.Exact.layerIndexEquiv configuration.laneDepth stage).surjective lane
  rcases position with ⟨group, branch, offset⟩
  have firstIndex :
      HTFFT.Exact.layerIndexEquiv depth (configuration.globalStage stage)
          { group := blockGroupEquiv configuration stage (cycle, group),
            branch := 0, offset := offset } =
        naturalLayout configuration
          (cycle, HTFFT.Exact.layerIndexEquiv configuration.laneDepth stage
            { group := group, branch := 0, offset := offset }) := by
    simpa only [globalPosition] using
      layerIndex_globalPosition configuration stage cycle
        ({ group := group, branch := 0, offset := offset } :
          HTFFT.Exact.LayerPosition configuration.laneDepth stage)
  have secondIndex :
      HTFFT.Exact.layerIndexEquiv depth (configuration.globalStage stage)
          { group := blockGroupEquiv configuration stage (cycle, group),
            branch := 1, offset := offset } =
        naturalLayout configuration
          (cycle, HTFFT.Exact.layerIndexEquiv configuration.laneDepth stage
            { group := group, branch := 1, offset := offset }) := by
    simpa only [globalPosition] using
      layerIndex_globalPosition configuration stage cycle
        ({ group := group, branch := 1, offset := offset } :
          HTFFT.Exact.LayerPosition configuration.laneDepth stage)
  rw [← layerIndex_globalPosition configuration stage cycle
    { group := group, branch := branch, offset := offset }]
  by_cases branchZero : branch = 0
  · subst branch
    rw [HTFFT.Fixed.butterflyLayer_first]
    simp only [globalPosition]
    rw [HTFFT.Fixed.butterflyLayer_first]
    rw [firstIndex, secondIndex]
    rfl
  · have branchOne : branch = 1 := by
      apply Fin.ext
      omega
    subst branch
    rw [HTFFT.Fixed.butterflyLayer_second]
    simp only [globalPosition]
    rw [HTFFT.Fixed.butterflyLayer_second]
    rw [firstIndex, secondIndex]
    rfl

@[simp] private theorem applyButterflyLayers_singleton
    (config : HTFFT.Fixed.Config depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (stage : Fin depth) (input : HTFFT.Fixed.Vector depth) :
    HTFFT.Fixed.applyButterflyLayers config table [stage] input =
      HTFFT.Fixed.butterflyLayer config table stage input :=
  rfl

/-- Every prefix consisting only of lane-local stages acts independently on
each cycle-sized block. -/
private theorem applyButterflyStagePrefix_block
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (cycle : Fin configuration.frameLength)
    (localInput : HTFFT.Fixed.Vector configuration.laneDepth)
    (globalInput : HTFFT.Fixed.Vector depth)
    (inputEqual : ∀ lane,
      localInput lane =
        globalInput (naturalLayout configuration (cycle, lane)))
    (boundary : HTFFT.Exact.LayerBoundary configuration.laneDepth)
    (lane : Fin configuration.laneCount) :
    HTFFT.Fixed.applyButterflyLayers configuration.unrolled.fixedConfig
        (configuration.prefixTable table)
        (HTFFT.Exact.butterflyStagePrefix configuration.laneDepth boundary)
        localInput lane =
      HTFFT.Fixed.applyButterflyLayers configuration.arithmetic.fixedConfig
        table
        (HTFFT.Exact.butterflyStagePrefix depth
          (configuration.globalBoundary boundary))
        globalInput (naturalLayout configuration (cycle, lane)) := by
  induction boundary using Fin.induction generalizing lane with
  | zero =>
      simpa [HTFFT.Exact.butterflyStagePrefix,
        HTFFT.Exact.butterflyStages] using inputEqual lane
  | succ stage inductionHypothesis =>
      have globalBoundarySucc :
          configuration.globalBoundary stage.succ =
            (configuration.globalStage stage).succ := by
        apply Fin.ext
        rfl
      rw [HTFFT.Exact.butterflyStagePrefix_boundarySucc,
        HTFFT.Fixed.applyButterflyLayers_append,
        globalBoundarySucc,
        HTFFT.Exact.butterflyStagePrefix_boundarySucc,
        HTFFT.Fixed.applyButterflyLayers_append,
        applyButterflyLayers_singleton,
        applyButterflyLayers_singleton]
      let localPrefix :=
        HTFFT.Fixed.applyButterflyLayers configuration.unrolled.fixedConfig
          (configuration.prefixTable table)
          (HTFFT.Exact.butterflyStagePrefix configuration.laneDepth
            stage.castSucc) localInput
      let globalPrefix :=
        HTFFT.Fixed.applyButterflyLayers configuration.arithmetic.fixedConfig
          table
          (HTFFT.Exact.butterflyStagePrefix depth
            (configuration.globalBoundary stage.castSucc)) globalInput
      have prefixesEqual : localPrefix = fun laneIndex =>
          globalPrefix (naturalLayout configuration (cycle, laneIndex)) := by
        funext laneIndex
        exact inductionHypothesis laneIndex
      rw [show
        HTFFT.Fixed.applyButterflyLayers configuration.unrolled.fixedConfig
            (configuration.prefixTable table)
            (HTFFT.Exact.butterflyStagePrefix configuration.laneDepth
              stage.castSucc) localInput = localPrefix from rfl,
        prefixesEqual]
      exact butterflyLayer_block configuration table stage globalPrefix cycle lane

private theorem decoded_initialReorder_cycle
    (configuration : Configuration depth)
    (input : InputFrame configuration)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    UnrolledFFTLayer.decodeVector
        (configuration.arithmetic.boundaryFormat 0)
        (InitialReorder.resultFrame configuration input cycle) lane =
      HTFFT.Exact.bitReverse (decodeInput configuration input)
        (naturalLayout configuration (cycle, lane)) := by
  simpa only [HTFFT.Exact.bitReverse, UnrolledFFTLayer.decodeVector,
    decodeInput] using
    congrArg
      (PipelinedFixedButterfly.decodeComplex
        (configuration.arithmetic.boundaryFormat 0).width)
      (initialReorder_cycle configuration input cycle lane)

/-- The independent unrolled networks are exactly the prefix of the global
fixed-point FFT when the input frame has first been globally reordered. -/
private theorem unrolledResultValue_block
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : InputFrame configuration)
    (cycle : Fin configuration.frameLength)
    (lane : Fin (2 ^ configuration.laneDepth)) :
    UnrolledFFTNetwork.resultValue configuration.unrolled
        (configuration.prefixTable table)
        (InitialReorder.resultFrame configuration input cycle) lane =
      HTFFT.Fixed.layeredPrefix configuration.arithmetic.fixedConfig table
        configuration.prefixBoundary (decodeInput configuration input)
        (naturalLayout configuration (cycle, lane)) := by
  unfold UnrolledFFTNetwork.resultValue
  rw [← HTFFT.Exact.butterflyStagePrefix_final
    configuration.laneDepth]
  unfold HTFFT.Fixed.layeredPrefix
  change
    HTFFT.Fixed.applyButterflyLayers configuration.unrolled.fixedConfig
        (configuration.prefixTable table)
        (HTFFT.Exact.butterflyStagePrefix configuration.laneDepth
          (Fin.last configuration.laneDepth))
        (UnrolledFFTLayer.decodeVector
          (configuration.arithmetic.boundaryFormat 0)
          (InitialReorder.resultFrame configuration input cycle)) lane =
      HTFFT.Fixed.applyButterflyLayers configuration.arithmetic.fixedConfig
        table
        (HTFFT.Exact.butterflyStagePrefix depth configuration.prefixBoundary)
        (HTFFT.Exact.bitReverse (decodeInput configuration input))
        (naturalLayout configuration (cycle, lane))
  exact applyButterflyStagePrefix_block configuration table cycle
    (UnrolledFFTLayer.decodeVector
      (configuration.arithmetic.boundaryFormat 0)
      (InitialReorder.resultFrame configuration input cycle))
    (HTFFT.Exact.bitReverse (decodeInput configuration input))
    (decoded_initialReorder_cycle configuration input cycle)
    (Fin.last configuration.laneDepth) lane

/-- Apply the lane-sized ascending butterfly network independently to every
cycle of the globally bit-reversed frame. -/
def unrolledResultFrame (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : InputFrame configuration) : PrefixFrame configuration :=
  fun cycle =>
    UnrolledFFTLayer.encodeVector
      (configuration.unrolled.boundaryFormat
        (Fin.last configuration.laneDepth))
      (UnrolledFFTNetwork.resultValue configuration.unrolled
        (configuration.prefixTable table) (input cycle))

private theorem unrolledResultValue_canonical
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : InputData configuration) :
    (fun index => HTFFT.Butterfly.Fixed.wrapComplex
      (configuration.unrolled.boundaryFormat
        (Fin.last configuration.laneDepth))
      (UnrolledFFTNetwork.resultValue configuration.unrolled
        (configuration.prefixTable table) input index)) =
      UnrolledFFTNetwork.resultValue configuration.unrolled
        (configuration.prefixTable table) input := by
  have inputCanonical :
      (fun index => HTFFT.Butterfly.Fixed.wrapComplex
        (configuration.unrolled.boundaryFormat 0)
        (UnrolledFFTLayer.decodeVector
          (configuration.unrolled.boundaryFormat 0) input index)) =
        UnrolledFFTLayer.decodeVector
          (configuration.unrolled.boundaryFormat 0) input := by
    funext index
    simp [UnrolledFFTLayer.decodeVector]
  simpa only [UnrolledFFTNetwork.resultValue,
      HTFFT.Exact.butterflyStagePrefix_final,
      FFTConfiguration.fixedConfig_boundaryFormat] using
    HTFFT.Fixed.wrapComplex_applyButterflyStagePrefix_of_canonical
      configuration.unrolled.fixedConfig
      (configuration.prefixTable table)
      (UnrolledFFTLayer.decodeVector
        (configuration.unrolled.boundaryFormat 0) input)
      inputCanonical (Fin.last configuration.laneDepth)

private theorem decode_unrolledResultFrame_cycle
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : InputFrame configuration)
    (cycle : Fin configuration.frameLength) :
    UnrolledFFTLayer.decodeVector
        (configuration.arithmetic.boundaryFormat configuration.prefixBoundary)
        (unrolledResultFrame configuration table
          (InitialReorder.resultFrame configuration input) cycle) =
      fun lane =>
        HTFFT.Fixed.layeredPrefix configuration.arithmetic.fixedConfig table
          configuration.prefixBoundary (decodeInput configuration input)
          (naturalLayout configuration (cycle, lane)) := by
  change UnrolledFFTLayer.decodeVector
      (configuration.unrolled.boundaryFormat
        (Fin.last configuration.laneDepth))
      (UnrolledFFTLayer.encodeVector
        (configuration.unrolled.boundaryFormat
          (Fin.last configuration.laneDepth))
        (UnrolledFFTNetwork.resultValue configuration.unrolled
          (configuration.prefixTable table)
          (InitialReorder.resultFrame configuration input cycle))) = _
  rw [UnrolledFFTLayer.decodeVector_encodeVector,
    unrolledResultValue_canonical]
  funext lane
  exact unrolledResultValue_block configuration table input cycle lane

/-- Decoding the cycle-parallel unrolled outputs gives precisely the global
fixed-point FFT state at the prefix boundary. -/
theorem decodePrefix_unrolledResultFrame
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : InputFrame configuration) :
    decodePrefix configuration
        (unrolledResultFrame configuration table
          (InitialReorder.resultFrame configuration input)) =
      HTFFT.Fixed.layeredPrefix configuration.arithmetic.fixedConfig table
        configuration.prefixBoundary (decodeInput configuration input) := by
  rw [decodePrefix_eq_decodeVector_unpackNatural]
  funext index
  obtain ⟨⟨cycle, lane⟩, rfl⟩ :=
    (naturalLayout configuration).surjective index
  have pointwise := congrFun
    (decode_unrolledResultFrame_cycle configuration table input cycle) lane
  simpa [Configuration.prefixGeometry_completed, unpackNatural,
    UnrolledFFTLayer.decodeVector] using pointwise

/-- The final physical-to-natural reorder is exactly a layout change. -/
@[simp] theorem finalReorder_encodeFinalPhysical
    (configuration : Configuration depth)
    (values : HTFFT.Fixed.Vector depth) :
    FinalReorder.resultFrame configuration
        (encodeFinalPhysical configuration values) =
      encodeOutput configuration values := by
  unfold FinalReorder.resultFrame encodeOutput
  rw [unpackFinalPhysical_encodeFinalPhysical]

/-- The four functional transforms in the top-level body compose to the
natural complete fixed-point FFT result. -/
theorem resultFrame_composition
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : InputFrame configuration) :
    FinalReorder.resultFrame configuration
        (FFTStageChain.resultFrame configuration table
          (unrolledResultFrame configuration table
            (InitialReorder.resultFrame configuration input))) =
      FFT.resultFrame configuration table input := by
  rw [FFTStageChain.resultFrame, FFTStageChain.resultValue,
    decodePrefix_unrolledResultFrame,
    finalReorder_encodeFinalPhysical]
  unfold FFT.resultFrame FFT.resultValue
  rw [HTFFT.Fixed.layeredFFT_split]

end HTFFT.Silean.FFT.Internal
