import HTFFT.Silean.FinalReorder.Internal.FinalReorderControlSchedule
import HTFFT.Silean.FinalReorder.Internal.FinalReorderStep
import HTFFT.Silean.FinalReorder.Internal.FinalReorderStructural
import Silean.Semantics.StructuralObservation

/-! End-to-end certification of the concrete final streamed reorder. -/

namespace HTFFT.Silean.FinalReorder.Internal
open FFT

open _root_.Silean
open _root_.Silean.Modules

private abbrev reorderStructure (depth : Nat)
    (configuration : Configuration depth) :=
  FinalReorder.moduleStructure depth configuration

private abbrev ControlInput (configuration : Configuration depth) :=
  (FinalReorder.Control.ports (addressWidth configuration)).inputs.Values

private abbrev ControlOutput (configuration : Configuration depth) :=
  (FinalReorder.Control.ports (addressWidth configuration)).outputs.Values

private def controlInputs
    {configuration : Configuration depth}
    (hierarchy : List (HierStep (reorderStructure depth configuration))) :
    List (ControlInput configuration) :=
  hierarchy.map fun step => (step.children .control).inputs

private def controlOutputs
    {configuration : Configuration depth}
    (hierarchy : List (HierStep (reorderStructure depth configuration))) :
    List (ControlOutput configuration) :=
  hierarchy.map fun step => (step.children .control).outputs

private def controlCycle (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    Fin (BitVector.cardinality (addressWidth configuration)) :=
  Fin.cast (addressCardinality configuration).symm cycle

@[simp] private theorem controlCycle_val
    (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    (controlCycle configuration cycle).val = cycle.val := rfl

private def frameCycleOfControl (configuration : Configuration depth)
    (cycle : Fin (BitVector.cardinality (addressWidth configuration))) :
    Fin configuration.frameLength :=
  Fin.cast (addressCardinality configuration) cycle

@[simp] private theorem frameCycleOfControl_val
    (configuration : Configuration depth)
    (cycle : Fin (BitVector.cardinality (addressWidth configuration))) :
    (frameCycleOfControl configuration cycle).val = cycle.val := rfl

private theorem control_write_schedule
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + configuration.frameLength +
      halfFrameLength configuration ≤ inputs.length)
    (starts : FramedLatency.Starts configuration.frameLength_pos
      (fun input : (FinalReorder.ports configuration).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window inputs start (by omega))) :
    (∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.writeObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + cycle.val, by
            rw [execution.length_eq]
            omega⟩).children .control).outputs =
        expectedWriteControls configuration cycle) ∧
      (∀ offset : Fin (halfFrameLength configuration),
        ∃ value : Nat, value ≤ offset.val ∧
          FinalReorder.Control.writeObservation (addressWidth configuration)
              ((hierarchy.get ⟨start + configuration.frameLength +
                offset.val, by rw [execution.length_eq]; omega⟩).children
                .control).outputs =
            FinalReorder.Control.writeControls (addressWidth configuration)
              (BitVector.ofNat (addressWidth configuration) value)) := by
  let childExecution := execution.child (.control)
  have childContract := FinalReorder.Control.contract_of_execution
    (addressWidth configuration) childExecution
  rcases childContract with ⟨controlInitial, controlFinal, controlTrace⟩
  rw [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
    at controlTrace
  change Trace (FinalReorder.Control.Transition (addressWidth configuration))
    controlInitial (controlInputs hierarchy) (controlOutputs hierarchy)
    controlFinal at controlTrace
  have childWithin : start + BitVector.cardinality
      (addressWidth configuration) + halfFrameLength configuration ≤
      (controlInputs hierarchy).length := by
    simp only [controlInputs, List.length_map]
    rw [execution.length_eq, addressCardinality]
    exact within
  have childStarts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos (addressWidth configuration))
      (fun input : ControlInput configuration =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window (length := BitVector.cardinality
        (addressWidth configuration)) (controlInputs hierarchy) start
        (by omega)) := by
    have childInputAt (offset : Fin (BitVector.cardinality
        (addressWidth configuration))) :
        (FramedLatency.window (controlInputs hierarchy) start (by omega)
          offset) .i_first =
        (FramedLatency.window inputs start (by omega)
          (frameCycleOfControl configuration offset)) .i_first := by
      have offsetBound : offset.val < configuration.frameLength := by
        rw [← addressCardinality]
        exact offset.isLt
      have hierarchyIn : start + offset.val < hierarchy.length := by
        rw [execution.length_eq]
        omega
      have inputIn : start + offset.val < inputs.length := by
        omega
      have solution := execution.solution_at
        (start + offset.val) hierarchyIn
      have wired := markerAndControl_of_solution solution
      have parentInput := execution.input_at
        (start + offset.val) hierarchyIn inputIn
      rw [parentInput] at wired
      simp only [FramedLatency.window_apply, controlInputs,
        List.get_eq_getElem, List.getElem_map] at wired ⊢
      exact wired.2.2.1
    constructor
    · change (FramedLatency.window (controlInputs hierarchy) start (by omega)
          ⟨0, by
            rw [BitVector.cardinality_eq_pow]
            exact Nat.two_pow_pos (addressWidth configuration)⟩) .i_first = true
      rw [childInputAt]
      exact starts.first
    · intro offset nonzero marked
      apply starts.not_first
        (frameCycleOfControl configuration offset)
      · simpa using nonzero
      · change (FramedLatency.window (controlInputs hierarchy) start (by omega)
            offset) .i_first = true at marked
        rwa [childInputAt] at marked
  have continuation :=
    FinalReorder.Control.write_observations_of_marked_window_with_continuation
      (addressWidth_pos configuration) controlTrace start
      (halfFrameLength configuration) (by
        rw [addressCardinality]
        have full := two_mul_halfFrameLength configuration
        omega)
      childWithin childStarts
  constructor
  · intro cycle
    have exactAt := FinalReorder.Control.write_observation_at_of_marked_window
      (addressWidth_pos configuration) controlTrace start (by omega)
      childStarts (controlCycle configuration cycle)
    have exactAt' : FinalReorder.Control.writeObservation
        (addressWidth configuration)
          (FramedLatency.window (controlOutputs hierarchy) start (by
            rw [controlTrace.length_eq]
            omega) (controlCycle configuration cycle)) =
      FinalReorder.Control.writeControls (addressWidth configuration)
        (BitVector.ofNat (addressWidth configuration) cycle.val) := by
      simpa only [controlCycle_val] using exactAt
    rw [writeControls_of_cycle configuration cycle] at exactAt'
    simpa only [FramedLatency.window_apply, controlOutputs,
      List.get_eq_getElem, List.getElem_map, controlCycle_val]
      using exactAt'
  · intro offset
    obtain ⟨value, bound, equal⟩ := continuation.2 offset
    refine ⟨value, bound, ?_⟩
    have frameOutputWithin : start + configuration.frameLength +
        halfFrameLength configuration ≤ (controlOutputs hierarchy).length := by
      rw [controlTrace.length_eq, ← addressCardinality]
      exact childWithin
    have windowsEqual :
        FramedLatency.window (length := halfFrameLength configuration)
            (controlOutputs hierarchy)
            (start + BitVector.cardinality (addressWidth configuration)) (by
              rw [controlTrace.length_eq]
              exact childWithin) =
          FramedLatency.window (controlOutputs hierarchy)
            (start + configuration.frameLength) frameOutputWithin := by
      apply FramedLatency.window_congr
      rw [addressCardinality]
    have equal' : FinalReorder.Control.writeObservation
        (addressWidth configuration)
          (FramedLatency.window (controlOutputs hierarchy)
            (start + configuration.frameLength) frameOutputWithin offset) =
        FinalReorder.Control.writeControls (addressWidth configuration)
          (BitVector.ofNat (addressWidth configuration) value) := by
      rw [← congrFun windowsEqual offset]
      exact equal
    simpa only [FramedLatency.window_apply, controlOutputs,
      List.get_eq_getElem, List.getElem_map] using equal'

private theorem marker_delay_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (time : Nat)
    (delayedIn : time + halfFrameLength configuration < hierarchy.length) :
    (hierarchy.get ⟨time + halfFrameLength configuration, delayedIn⟩).outputs
        .o_first =
      (hierarchy.get ⟨time, by omega⟩).inputs .i_first ∧
    ((hierarchy.get ⟨time + halfFrameLength configuration, delayedIn⟩).children
        .control).inputs .i_readFirst =
      (hierarchy.get ⟨time, by omega⟩).inputs .i_first := by
  let childExecution := execution.child (.markerDelay)
  have childContract := ShiftRegister.contract_of_execution .bit
    configuration.finalReorderLatency
    configuration.finalReorderLatency_pos childExecution
  have childInputIn : time <
      (List.map (fun step => (step.children .markerDelay).inputs)
        hierarchy).length := by
    rw [List.length_map]
    omega
  have childOutputIn : time + configuration.finalReorderLatency <
      (List.map (fun step => (step.children .markerDelay).outputs)
        hierarchy).length := by
    rw [List.length_map]
    exact delayedIn
  have delayed := FixedLatency.relation_at_of_trace childExecution
    childContract time childInputIn childOutputIn
  simp only [List.get_eq_getElem, List.getElem_map] at delayed
  have sourceSolution := execution.solution_at time (by omega)
  have delayedSolution := execution.solution_at
    (time + halfFrameLength configuration) delayedIn
  have sourceWiring := markerAndControl_of_solution sourceSolution
  have delayedWiring := markerAndControl_of_solution delayedSolution
  change ((hierarchy.get
    ⟨time + halfFrameLength configuration, delayedIn⟩).children
      .markerDelay).outputs .output =
      ((hierarchy.get ⟨time, by omega⟩).children
        .markerDelay).inputs .input at delayed
  refine ⟨?_, ?_⟩
  · rw [delayedWiring.2.1, delayed, sourceWiring.1]
  · rw [delayedWiring.2.2.2, delayed, sourceWiring.1]

private theorem control_read_schedule
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + halfFrameLength configuration +
      configuration.frameLength ≤ inputs.length)
    (starts : FramedLatency.Starts configuration.frameLength_pos
      (fun input : (FinalReorder.ports configuration).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window inputs start (by omega))) :
    ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.readObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + halfFrameLength configuration +
            cycle.val, by rw [execution.length_eq]; omega⟩).children
            .control).outputs =
        expectedReadControls configuration cycle := by
  let childExecution := execution.child (.control)
  have childContract := FinalReorder.Control.contract_of_execution
    (addressWidth configuration) childExecution
  rcases childContract with ⟨controlInitial, controlFinal, controlTrace⟩
  rw [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
    at controlTrace
  change Trace (FinalReorder.Control.Transition (addressWidth configuration))
    controlInitial (controlInputs hierarchy) (controlOutputs hierarchy)
    controlFinal at controlTrace
  have childWithin : start + halfFrameLength configuration +
      BitVector.cardinality (addressWidth configuration) ≤
      (controlInputs hierarchy).length := by
    simp only [controlInputs, List.length_map]
    rw [execution.length_eq, addressCardinality]
    exact within
  have readStarts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos (addressWidth configuration))
      (fun input : ControlInput configuration =>
        (show Bool from input .i_readFirst) = true)
      (FramedLatency.window (length := BitVector.cardinality
        (addressWidth configuration)) (controlInputs hierarchy)
        (start + halfFrameLength configuration) childWithin) := by
    have markerAt (offset : Fin (BitVector.cardinality
        (addressWidth configuration))) :
        (FramedLatency.window (controlInputs hierarchy)
          (start + halfFrameLength configuration) childWithin offset)
            .i_readFirst =
          (FramedLatency.window inputs start (by omega)
            (frameCycleOfControl configuration offset)) .i_first := by
      have offsetBound : offset.val < configuration.frameLength := by
        rw [← addressCardinality]
        exact offset.isLt
      have delayedIn : start + offset.val +
          halfFrameLength configuration < hierarchy.length := by
        rw [execution.length_eq]
        omega
      have delayed := marker_delay_at configuration execution
        (start + offset.val) delayedIn
      have parentInput := execution.input_at (start + offset.val) (by
        rw [execution.length_eq]
        omega) (by omega)
      rw [parentInput] at delayed
      simpa only [FramedLatency.window_apply, controlInputs,
        List.get_eq_getElem, List.getElem_map, frameCycleOfControl_val,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using delayed.2
    constructor
    · change (FramedLatency.window (controlInputs hierarchy)
          (start + halfFrameLength configuration) childWithin
          ⟨0, by
            rw [BitVector.cardinality_eq_pow]
            exact Nat.two_pow_pos (addressWidth configuration)⟩)
            .i_readFirst = true
      rw [markerAt]
      exact starts.first
    · intro offset nonzero marked
      apply starts.not_first (frameCycleOfControl configuration offset)
      · simpa using nonzero
      · change (FramedLatency.window (controlInputs hierarchy)
            (start + halfFrameLength configuration) childWithin offset)
              .i_readFirst = true at marked
        rwa [markerAt] at marked
  intro cycle
  have exactAt := FinalReorder.Control.read_observation_at_of_marked_window
    (addressWidth_pos configuration) controlTrace
    (start + halfFrameLength configuration) childWithin readStarts
    (controlCycle configuration cycle)
  have exactAt' : FinalReorder.Control.readObservation
      (addressWidth configuration)
        (FramedLatency.window (controlOutputs hierarchy)
          (start + halfFrameLength configuration) (by
            rw [controlTrace.length_eq]
            exact childWithin) (controlCycle configuration cycle)) =
      FinalReorder.Control.readControls (addressWidth configuration)
        (BitVector.ofNat (addressWidth configuration) cycle.val) := by
    simpa only [controlCycle_val] using exactAt
  rw [readControls_of_cycle configuration cycle] at exactAt'
  simpa only [FramedLatency.window_apply, controlOutputs,
    List.get_eq_getElem, List.getElem_map, controlCycle_val]
    using exactAt'

private theorem bank0_write_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + configuration.frameLength ≤ hierarchy.length)
    (writeSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.writeObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
            .control).outputs =
        expectedWriteControls configuration cycle)
    (cycle : Fin configuration.frameLength) :
    let step := hierarchy.get ⟨start + cycle.val, by omega⟩
    (step.children .bank0).inputs .writeEnable = true ∧
      (step.children .bank0).inputs .writeAddress =
        BitVector.ofNat (addressWidth configuration)
          (firstBankWriteAddress configuration cycle).val ∧
      (step.children .bank0).inputs .writeValue =
        if cycle.val % 2 = 0 then
          fun lane => step.inputs .i_data (lowerLane configuration lane)
        else
          fun lane => step.inputs .i_data (upperLane configuration lane) := by
  dsimp only
  have solution := execution.solution_at (start + cycle.val) (by omega)
  have wired := bank0Inputs_of_solution solution
  have controls := writeSchedule cycle
  change
    { address0 := _
      address1 := _
      swap := _
      bypass := _ } = expectedWriteControls configuration cycle at controls
  have address := congrArg FinalReorder.Control.WriteObservation.address0 controls
  have swap := congrArg FinalReorder.Control.WriteObservation.swap controls
  simp only [expectedWriteControls] at address swap
  refine ⟨wired.1, ?_, ?_⟩
  · rw [wired.2.1, address]
  · rw [wired.2.2.1, swap]
    by_cases even : cycle.val % 2 = 0
    · simp [even]
    · have odd : cycle.val % 2 = 1 := by
        have remainder := Nat.mod_lt cycle.val (by omega : 0 < 2)
        omega
      simp [odd]

private theorem bank1_write_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + configuration.frameLength ≤ hierarchy.length)
    (writeSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.writeObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
            .control).outputs =
        expectedWriteControls configuration cycle)
    (cycle : Fin configuration.frameLength) :
    let step := hierarchy.get ⟨start + cycle.val, by omega⟩
    (step.children .bank1).inputs .writeEnable = true ∧
      (step.children .bank1).inputs .writeAddress =
        BitVector.ofNat (addressWidth configuration)
          (secondBankWriteAddress configuration cycle).val ∧
      (step.children .bank1).inputs .writeValue =
        if cycle.val % 2 = 0 then
          fun lane => step.inputs .i_data (upperLane configuration lane)
        else
          fun lane => step.inputs .i_data (lowerLane configuration lane) := by
  dsimp only
  have solution := execution.solution_at (start + cycle.val) (by omega)
  have wired := bank1Inputs_of_solution solution
  have controls := writeSchedule cycle
  change
    { address0 := _
      address1 := _
      swap := _
      bypass := _ } = expectedWriteControls configuration cycle at controls
  have address := congrArg FinalReorder.Control.WriteObservation.address1 controls
  have swap := congrArg FinalReorder.Control.WriteObservation.swap controls
  simp only [expectedWriteControls] at address swap
  refine ⟨wired.1, ?_, ?_⟩
  · rw [wired.2.1, address]
  · rw [wired.2.2.1, swap]
    by_cases even : cycle.val % 2 = 0
    · simp [even]
    · have odd : cycle.val % 2 = 1 := by
        have remainder := Nat.mod_lt cycle.val (by omega : 0 < 2)
        omega
      simp [odd]

private theorem bank_read_address_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + halfFrameLength configuration +
      configuration.frameLength ≤ hierarchy.length)
    (readSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.readObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + halfFrameLength configuration +
            cycle.val, by omega⟩).children .control).outputs =
        expectedReadControls configuration cycle)
    (cycle : Fin configuration.frameLength) :
    let step := hierarchy.get ⟨start + halfFrameLength configuration +
      cycle.val, by omega⟩
    (step.children .bank0).inputs (.readAddress 0) =
        BitVector.ofNat (addressWidth configuration) cycle.val ∧
      (step.children .bank1).inputs (.readAddress 0) =
        BitVector.ofNat (addressWidth configuration) cycle.val := by
  dsimp only
  have solution := execution.solution_at
    (start + halfFrameLength configuration + cycle.val) (by omega)
  have bank0 := bank0Inputs_of_solution solution
  have bank1 := bank1Inputs_of_solution solution
  have controls := readSchedule cycle
  change
    { address := _
      swap := _ } = expectedReadControls configuration cycle at controls
  have address := congrArg FinalReorder.Control.ReadObservation.address controls
  simp only [expectedReadControls] at address
  exact ⟨bank0.2.2.2.trans address, bank1.2.2.2.trans address⟩

private theorem continuation_write_addresses_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + configuration.frameLength +
      halfFrameLength configuration ≤ hierarchy.length)
    (continuation : ∀ offset : Fin (halfFrameLength configuration),
      ∃ value : Nat, value ≤ offset.val ∧
        FinalReorder.Control.writeObservation (addressWidth configuration)
            ((hierarchy.get ⟨start + configuration.frameLength +
              offset.val, by omega⟩).children .control).outputs =
          FinalReorder.Control.writeControls (addressWidth configuration)
            (BitVector.ofNat (addressWidth configuration) value))
    (offset : Fin (halfFrameLength configuration)) :
    ∃ cycle : Fin configuration.frameLength,
      cycle.val ≤ offset.val ∧
      let step := hierarchy.get ⟨start + configuration.frameLength +
        offset.val, by omega⟩
      (step.children .bank0).inputs .writeAddress =
          BitVector.ofNat (addressWidth configuration)
            (firstBankWriteAddress configuration cycle).val ∧
        (step.children .bank1).inputs .writeAddress =
          BitVector.ofNat (addressWidth configuration)
            (secondBankWriteAddress configuration cycle).val := by
  obtain ⟨value, valueBound, controls⟩ := continuation offset
  have valueInFrame : value < configuration.frameLength := by
    have halfPositive := halfFrameLength_pos configuration
    have full := two_mul_halfFrameLength configuration
    omega
  let cycle : Fin configuration.frameLength := ⟨value, valueInFrame⟩
  refine ⟨cycle, valueBound, ?_⟩
  dsimp only
  have solution := execution.solution_at
    (start + configuration.frameLength + offset.val) (by omega)
  have bank0 := bank0Inputs_of_solution solution
  have bank1 := bank1Inputs_of_solution solution
  have expected := writeControls_of_cycle configuration cycle
  have controls' : FinalReorder.Control.writeObservation
      (addressWidth configuration)
        ((hierarchy.get ⟨start + configuration.frameLength + offset.val,
          by omega⟩).children .control).outputs =
      expectedWriteControls configuration cycle := by
    rw [controls, expected]
  have address0 := congrArg FinalReorder.Control.WriteObservation.address0
    controls'
  have address1 := congrArg FinalReorder.Control.WriteObservation.address1
    controls'
  simp only [expectedWriteControls] at address0 address1
  exact ⟨bank0.2.1.trans address0, bank1.2.1.trans address1⟩

private theorem addressIndex_injective
    (configuration : Configuration depth) :
    Function.Injective (fun cycle : Fin configuration.frameLength =>
      BitVector.toIndex (addressWidth configuration)
        (BitVector.ofNat (addressWidth configuration) cycle.val)) := by
  intro left right equal
  apply Fin.ext
  have numeric := congrArg Fin.val equal
  simp only [BitVector.toIndex_val, BitVector.toNat_ofNat] at numeric
  have leftBound : left.val <
      BitVector.cardinality (addressWidth configuration) := by
    rw [addressCardinality]
    exact left.isLt
  have rightBound : right.val <
      BitVector.cardinality (addressWidth configuration) := by
    rw [addressCardinality]
    exact right.isLt
  rwa [Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound] at numeric

/-- A register bank following an injective frame write schedule returns the
selected earlier frame write. The continuation premise is deliberately only
as strong as needed for a legal back-to-back frame: its counter may restart,
but cannot yet have reached the selected old-frame source cycle. -/
private theorem scheduled_bank_read
    (configuration : Configuration depth)
    {initial final :
      (RegisterBank.stateMap (halfVectorType configuration)
        (addressWidth configuration)).Values}
    {bankInputs : List (RegisterBank.InputValues
      (halfVectorType configuration) (addressWidth configuration) 1)}
    {bankOutputs : List (RegisterBank.OutputValues
      (halfVectorType configuration) 1)}
    (trace : Trace (RegisterBank.cycleContract
      (halfVectorType configuration) (addressWidth configuration) 1).Transition
      initial bankInputs bankOutputs final)
    (start : Nat)
    (source outputCycle : Fin configuration.frameLength)
    (writeAddress : Fin configuration.frameLength →
      Fin configuration.frameLength)
    (writeAddressInjective : Function.Injective writeAddress)
    (addressMatches : writeAddress source = outputCycle)
    (within : start + halfFrameLength configuration +
      configuration.frameLength ≤ bankInputs.length)
    (writeBeforeRead : source.val <
      halfFrameLength configuration + outputCycle.val)
    (frameInput : ∀ cycle : Fin configuration.frameLength,
      let input := bankInputs.get ⟨start + cycle.val, by omega⟩
      input .writeEnable = true ∧
        input .writeAddress =
          BitVector.ofNat (addressWidth configuration)
            (writeAddress cycle).val)
    (readAddress :
      bankInputs.get ⟨start + halfFrameLength configuration +
        outputCycle.val, by omega⟩ (.readAddress 0) =
        BitVector.ofNat (addressWidth configuration) outputCycle.val)
    (continuationAddress : ∀ offset : Fin (halfFrameLength configuration),
      ∃ cycle : Fin configuration.frameLength,
        cycle.val ≤ offset.val ∧
        bankInputs.get ⟨start + configuration.frameLength + offset.val,
          by omega⟩ .writeAddress =
            BitVector.ofNat (addressWidth configuration)
              (writeAddress cycle).val)
    (continuationBeforeSource : ∀ offset : Fin (halfFrameLength configuration),
      start + configuration.frameLength + offset.val <
          start + halfFrameLength configuration + outputCycle.val →
        offset.val < source.val) :
    bankOutputs.get ⟨start + halfFrameLength configuration +
      outputCycle.val, by rw [trace.length_eq]; omega⟩ (.readValue 0) =
      bankInputs.get ⟨start + source.val, by omega⟩ .writeValue := by
  let writePosition := start + source.val
  let readPosition := start + halfFrameLength configuration + outputCycle.val
  apply RegisterBank.read_after_write trace 0 writePosition readPosition
    (by
      dsimp only [writePosition, readPosition]
      omega)
    (by
      dsimp only [readPosition]
      have outputBound := outputCycle.isLt
      omega)
  · dsimp only [writePosition]
    exact (frameInput source).1
  · dsimp only [writePosition, readPosition]
    unfold RegisterBank.writeIndex
    rw [readAddress, (frameInput source).2, addressMatches]
  · intro position afterWrite beforeRead _enabled sameIndex
    by_cases inFrame : position < start + configuration.frameLength
    · let cycle : Fin configuration.frameLength :=
        ⟨position - start, by omega⟩
      have positionEqual : start + cycle.val = position := by
        dsimp only [cycle]
        omega
      have addressAt := (frameInput cycle).2
      simp only [positionEqual] at addressAt
      have targetAddress := (frameInput source).2
      change BitVector.toIndex (addressWidth configuration)
          (bankInputs.get ⟨position, by omega⟩ .writeAddress) =
        BitVector.toIndex (addressWidth configuration)
          (bankInputs.get ⟨start + source.val, by omega⟩ .writeAddress)
        at sameIndex
      have scheduledIndex : BitVector.toIndex (addressWidth configuration)
          (BitVector.ofNat (addressWidth configuration)
            (writeAddress cycle).val) =
        BitVector.toIndex (addressWidth configuration)
          (BitVector.ofNat (addressWidth configuration)
            (writeAddress source).val) := by
        rw [← addressAt, ← targetAddress]
        exact sameIndex
      have cycleEqual := writeAddressInjective
        (addressIndex_injective configuration scheduledIndex)
      have numeric := congrArg Fin.val cycleEqual
      dsimp only [cycle, writePosition] at numeric afterWrite
      omega
    · have afterFrame : start + configuration.frameLength ≤ position := by
        omega
      let offset : Fin (halfFrameLength configuration) :=
        ⟨position - (start + configuration.frameLength), by
          dsimp only [readPosition] at beforeRead
          have full := two_mul_halfFrameLength configuration
          omega⟩
      have positionEqual :
          start + configuration.frameLength + offset.val = position := by
        dsimp only [offset]
        omega
      obtain ⟨cycle, cycleBound, addressAt⟩ :=
        continuationAddress offset
      simp only [positionEqual] at addressAt
      have targetAddress := (frameInput source).2
      change BitVector.toIndex (addressWidth configuration)
          (bankInputs.get ⟨position, by omega⟩ .writeAddress) =
        BitVector.toIndex (addressWidth configuration)
          (bankInputs.get ⟨start + source.val, by omega⟩ .writeAddress)
        at sameIndex
      have scheduledIndex : BitVector.toIndex (addressWidth configuration)
          (BitVector.ofNat (addressWidth configuration)
            (writeAddress cycle).val) =
        BitVector.toIndex (addressWidth configuration)
          (BitVector.ofNat (addressWidth configuration)
            (writeAddress source).val) := by
        rw [← addressAt, ← targetAddress]
        exact sameIndex
      have cycleEqual := writeAddressInjective
        (addressIndex_injective configuration scheduledIndex)
      have numeric := congrArg Fin.val cycleEqual
      have offsetBefore := continuationBeforeSource offset (by
        rw [positionEqual]
        exact beforeRead)
      omega

private theorem bank0_read_from_source
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + halfFrameLength configuration +
      configuration.frameLength ≤ hierarchy.length)
    (writeSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.writeObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
            .control).outputs =
        expectedWriteControls configuration cycle)
    (continuation : ∀ offset : Fin (halfFrameLength configuration),
      ∃ value : Nat, value ≤ offset.val ∧
        FinalReorder.Control.writeObservation (addressWidth configuration)
            ((hierarchy.get ⟨start + configuration.frameLength +
              offset.val, by omega⟩).children .control).outputs =
          FinalReorder.Control.writeControls (addressWidth configuration)
            (BitVector.ofNat (addressWidth configuration) value))
    (readSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.readObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + halfFrameLength configuration +
            cycle.val, by omega⟩).children .control).outputs =
        expectedReadControls configuration cycle)
    (source outputCycle : Fin configuration.frameLength)
    (addressMatches : firstBankWriteAddress configuration source = outputCycle)
    (writeBeforeRead : source.val <
      halfFrameLength configuration + outputCycle.val)
    (continuationBeforeSource : ∀ offset : Fin (halfFrameLength configuration),
      start + configuration.frameLength + offset.val <
          start + halfFrameLength configuration + outputCycle.val →
        offset.val < source.val) :
    ((hierarchy.get ⟨start + halfFrameLength configuration + outputCycle.val,
      by omega⟩).children .bank0).outputs (.readValue 0) =
      ((hierarchy.get ⟨start + source.val, by omega⟩).children
        .bank0).inputs .writeValue := by
  let bankExecution := execution.child (.bank0)
  simp only [FinalReorder.structuralChildren] at bankExecution
  obtain ⟨bankInitial, bankFinal, bankTrace⟩ :=
    (RegisterBank.certification (halfVectorType configuration)
      (addressWidth configuration) 1).accepts_of_executes bankExecution
  have frameInput : ∀ cycle : Fin configuration.frameLength,
      let input := (hierarchy.map fun step =>
        (step.children .bank0).inputs).get ⟨start + cycle.val, by
          simp only [List.length_map]
          omega⟩
      input .writeEnable = true ∧
        input .writeAddress =
          BitVector.ofNat (addressWidth configuration)
            (firstBankWriteAddress configuration cycle).val := by
    intro cycle
    have atCycle := bank0_write_at configuration execution start (by omega)
      writeSchedule cycle
    simpa only [List.get_eq_getElem, List.getElem_map] using
      And.intro atCycle.1 atCycle.2.1
  have readAddress := (bank_read_address_at configuration execution start within
    readSchedule outputCycle).1
  have continuationAddress : ∀ offset : Fin (halfFrameLength configuration),
      ∃ cycle : Fin configuration.frameLength,
        cycle.val ≤ offset.val ∧
        (hierarchy.map fun step =>
          (step.children .bank0).inputs).get
            ⟨start + configuration.frameLength + offset.val, by
              simp only [List.length_map]
              omega⟩ .writeAddress =
          BitVector.ofNat (addressWidth configuration)
            (firstBankWriteAddress configuration cycle).val := by
    intro offset
    obtain ⟨cycle, bound, bank0Address, _⟩ :=
      continuation_write_addresses_at configuration execution start (by omega)
        continuation offset
    exact ⟨cycle, bound, by
      simpa only [List.get_eq_getElem, List.getElem_map] using bank0Address⟩
  have result := scheduled_bank_read configuration bankTrace start source
    outputCycle (firstBankWriteAddress configuration)
    (firstBankWriteAddress_injective configuration) addressMatches (by
      simp only [List.length_map]
      exact within) writeBeforeRead frameInput (by
        simpa only [List.get_eq_getElem, List.getElem_map] using readAddress)
      continuationAddress continuationBeforeSource
  simpa only [List.get_eq_getElem, List.getElem_map] using result

private theorem bank1_read_from_source
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + halfFrameLength configuration +
      configuration.frameLength ≤ hierarchy.length)
    (writeSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.writeObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
            .control).outputs =
        expectedWriteControls configuration cycle)
    (continuation : ∀ offset : Fin (halfFrameLength configuration),
      ∃ value : Nat, value ≤ offset.val ∧
        FinalReorder.Control.writeObservation (addressWidth configuration)
            ((hierarchy.get ⟨start + configuration.frameLength +
              offset.val, by omega⟩).children .control).outputs =
          FinalReorder.Control.writeControls (addressWidth configuration)
            (BitVector.ofNat (addressWidth configuration) value))
    (readSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.readObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + halfFrameLength configuration +
            cycle.val, by omega⟩).children .control).outputs =
        expectedReadControls configuration cycle)
    (source outputCycle : Fin configuration.frameLength)
    (addressMatches : secondBankWriteAddress configuration source = outputCycle)
    (writeBeforeRead : source.val <
      halfFrameLength configuration + outputCycle.val)
    (continuationBeforeSource : ∀ offset : Fin (halfFrameLength configuration),
      start + configuration.frameLength + offset.val <
          start + halfFrameLength configuration + outputCycle.val →
        offset.val < source.val) :
    ((hierarchy.get ⟨start + halfFrameLength configuration + outputCycle.val,
      by omega⟩).children .bank1).outputs (.readValue 0) =
      ((hierarchy.get ⟨start + source.val, by omega⟩).children
        .bank1).inputs .writeValue := by
  let bankExecution := execution.child (.bank1)
  simp only [FinalReorder.structuralChildren] at bankExecution
  obtain ⟨bankInitial, bankFinal, bankTrace⟩ :=
    (RegisterBank.certification (halfVectorType configuration)
      (addressWidth configuration) 1).accepts_of_executes bankExecution
  have frameInput : ∀ cycle : Fin configuration.frameLength,
      let input := (hierarchy.map fun step =>
        (step.children .bank1).inputs).get ⟨start + cycle.val, by
          simp only [List.length_map]
          omega⟩
      input .writeEnable = true ∧
        input .writeAddress =
          BitVector.ofNat (addressWidth configuration)
            (secondBankWriteAddress configuration cycle).val := by
    intro cycle
    have atCycle := bank1_write_at configuration execution start (by omega)
      writeSchedule cycle
    simpa only [List.get_eq_getElem, List.getElem_map] using
      And.intro atCycle.1 atCycle.2.1
  have readAddress := (bank_read_address_at configuration execution start within
    readSchedule outputCycle).2
  have continuationAddress : ∀ offset : Fin (halfFrameLength configuration),
      ∃ cycle : Fin configuration.frameLength,
        cycle.val ≤ offset.val ∧
        (hierarchy.map fun step =>
          (step.children .bank1).inputs).get
            ⟨start + configuration.frameLength + offset.val, by
              simp only [List.length_map]
              omega⟩ .writeAddress =
          BitVector.ofNat (addressWidth configuration)
            (secondBankWriteAddress configuration cycle).val := by
    intro offset
    obtain ⟨cycle, bound, _, bank1Address⟩ :=
      continuation_write_addresses_at configuration execution start (by omega)
        continuation offset
    exact ⟨cycle, bound, by
      simpa only [List.get_eq_getElem, List.getElem_map] using bank1Address⟩
  have result := scheduled_bank_read configuration bankTrace start source
    outputCycle (secondBankWriteAddress configuration)
    (secondBankWriteAddress_injective configuration) addressMatches (by
      simp only [List.length_map]
      exact within) writeBeforeRead frameInput (by
        simpa only [List.get_eq_getElem, List.getElem_map] using readAddress)
      continuationAddress continuationBeforeSource
  simpa only [List.get_eq_getElem, List.getElem_map] using result

private theorem readSwap_at
    (configuration : Configuration depth)
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (start : Nat)
    (within : start + halfFrameLength configuration +
      configuration.frameLength ≤ hierarchy.length)
    (readSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.readObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + halfFrameLength configuration +
            cycle.val, by omega⟩).children .control).outputs =
        expectedReadControls configuration cycle)
    (cycle : Fin configuration.frameLength) :
    ((hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
      by omega⟩).children .control).outputs .o_readSwap =
        decide (halfFrameLength configuration ≤ cycle.val) := by
  change (show Bool from ((hierarchy.get
    ⟨start + halfFrameLength configuration + cycle.val, by omega⟩).children
      .control).outputs .o_readSwap) = _
  have controls := readSchedule cycle
  have swap := congrArg FinalReorder.Control.ReadObservation.swap controls
  simpa only [expectedReadControls,
    FinalReorder.Control.readObservation] using swap

private theorem markedBypass_at
    (configuration : Configuration depth)
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (start : Nat)
    (within : start + configuration.frameLength ≤ hierarchy.length)
    (writeSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.writeObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
            .control).outputs =
        expectedWriteControls configuration cycle)
    (cycle : Fin configuration.frameLength) :
    ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
      .control).outputs .o_bypass =
        decide (cycle.val + 1 = configuration.frameLength) := by
  change (show Bool from ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
    .control).outputs .o_bypass) = _
  have controls := writeSchedule cycle
  have bypass := congrArg FinalReorder.Control.WriteObservation.bypass controls
  simpa only [expectedWriteControls,
    FinalReorder.Control.writeObservation] using bypass

private theorem continuationBypass_at
    (configuration : Configuration depth)
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (start : Nat)
    (within : start + configuration.frameLength +
      halfFrameLength configuration ≤ hierarchy.length)
    (continuation : ∀ offset : Fin (halfFrameLength configuration),
      ∃ value : Nat, value ≤ offset.val ∧
        FinalReorder.Control.writeObservation (addressWidth configuration)
            ((hierarchy.get ⟨start + configuration.frameLength +
              offset.val, by omega⟩).children .control).outputs =
          FinalReorder.Control.writeControls (addressWidth configuration)
            (BitVector.ofNat (addressWidth configuration) value))
    (offset : Fin (halfFrameLength configuration)) :
    ((hierarchy.get ⟨start + configuration.frameLength + offset.val,
      by omega⟩).children .control).outputs .o_bypass = false := by
  obtain ⟨value, valueBound, controls⟩ := continuation offset
  have valueInAddress : value <
      BitVector.cardinality (addressWidth configuration) := by
    rw [addressCardinality]
    have full := two_mul_halfFrameLength configuration
    omega
  have bypass := congrArg FinalReorder.Control.WriteObservation.bypass controls
  change ((hierarchy.get ⟨start + configuration.frameLength + offset.val,
    by omega⟩).children .control).outputs .o_bypass =
      FinalReorder.Control.bypass (addressWidth configuration)
        (BitVector.ofNat (addressWidth configuration) value) at bypass
  rw [FinalReorder.Control.bypass_ofNat _ _ valueInAddress] at bypass
  have notLast : value ≠
      BitVector.cardinality (addressWidth configuration) - 1 := by
    rw [addressCardinality]
    have full := two_mul_halfFrameLength configuration
    have positive := halfFrameLength_pos configuration
    omega
  have notLastPow : value ≠ 2 ^ addressWidth configuration - 1 := by
    simpa only [BitVector.cardinality_eq_pow] using notLast
  simpa [notLastPow] using bypass

private theorem first_lower_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + halfFrameLength configuration +
      configuration.frameLength ≤ hierarchy.length)
    (writeSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.writeObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
            .control).outputs = expectedWriteControls configuration cycle)
    (continuation : ∀ offset : Fin (halfFrameLength configuration),
      ∃ value : Nat, value ≤ offset.val ∧
        FinalReorder.Control.writeObservation (addressWidth configuration)
            ((hierarchy.get ⟨start + configuration.frameLength +
              offset.val, by omega⟩).children .control).outputs =
          FinalReorder.Control.writeControls (addressWidth configuration)
            (BitVector.ofNat (addressWidth configuration) value))
    (readSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.readObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + halfFrameLength configuration +
            cycle.val, by omega⟩).children .control).outputs =
        expectedReadControls configuration cycle)
    (cycle : Fin (halfFrameLength configuration))
    (lane : Fin (halfLaneCount configuration)) :
    (hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
      by
        have full := two_mul_halfFrameLength configuration
        omega⟩).outputs .o_data (lowerLane configuration lane) =
      (hierarchy.get ⟨start + (evenInputCycle configuration cycle).val,
        by
          have full := two_mul_halfFrameLength configuration
          omega⟩).inputs .i_data (lowerLane configuration lane) := by
  have full := two_mul_halfFrameLength configuration
  let outputCycle := firstOutputCycle configuration cycle
  let source := evenInputCycle configuration cycle
  have bankRead := bank0_read_from_source configuration execution start within
    writeSchedule continuation readSchedule source outputCycle
    (by simp [source, outputCycle])
    (by
      dsimp only [source, outputCycle]
      exact even_write_before_first_read configuration cycle)
    (by
      intro offset before
      change start + configuration.frameLength + offset.val <
        start + halfFrameLength configuration + cycle.val at before
      omega)
  have sourceWrite := bank0_write_at configuration execution start (by omega)
    writeSchedule source
  have targetSolution := execution.solution_at
    (start + halfFrameLength configuration + cycle.val) (by omega)
  have outputValue :=
    (outputHalves_of_solution targetSolution).1 lane
  have swap := readSwap_at configuration start within readSchedule outputCycle
  have notSecond : ¬ halfFrameLength configuration ≤ outputCycle.val := by
    dsimp only [outputCycle]
    exact Nat.not_le_of_gt cycle.isLt
  have bankRead' :
      ((hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
        by omega⟩).children .bank0).outputs (.readValue 0) =
      ((hierarchy.get ⟨start + source.val, by omega⟩).children
        .bank0).inputs .writeValue := by
    simpa only [outputCycle, firstOutputCycle_val] using bankRead
  have swapFalse :
      ((hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
        by omega⟩).children .control).outputs .o_readSwap = false := by
    simp only [outputCycle, firstOutputCycle_val] at swap
    rw [swap]
    simp [Nat.not_le_of_gt cycle.isLt]
  rw [swapFalse] at outputValue
  rw [outputValue, bankRead', sourceWrite.2.2]
  simp [source, evenInputCycle]

private theorem second_upper_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + halfFrameLength configuration +
      configuration.frameLength ≤ hierarchy.length)
    (writeSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.writeObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
            .control).outputs = expectedWriteControls configuration cycle)
    (continuation : ∀ offset : Fin (halfFrameLength configuration),
      ∃ value : Nat, value ≤ offset.val ∧
        FinalReorder.Control.writeObservation (addressWidth configuration)
            ((hierarchy.get ⟨start + configuration.frameLength +
              offset.val, by omega⟩).children .control).outputs =
          FinalReorder.Control.writeControls (addressWidth configuration)
            (BitVector.ofNat (addressWidth configuration) value))
    (readSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.readObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + halfFrameLength configuration +
            cycle.val, by omega⟩).children .control).outputs =
        expectedReadControls configuration cycle)
    (cycle : Fin (halfFrameLength configuration))
    (lane : Fin (halfLaneCount configuration)) :
    (hierarchy.get ⟨start + configuration.frameLength + cycle.val,
      by
        have full := two_mul_halfFrameLength configuration
        omega⟩).outputs .o_data (upperLane configuration lane) =
      (hierarchy.get ⟨start + (oddInputCycle configuration cycle).val,
        by
          have full := two_mul_halfFrameLength configuration
          omega⟩).inputs .i_data (upperLane configuration lane) := by
  have full := two_mul_halfFrameLength configuration
  let outputCycle := secondOutputCycle configuration cycle
  let source := oddInputCycle configuration cycle
  have bankRead := bank0_read_from_source configuration execution start within
    writeSchedule continuation readSchedule source outputCycle
    (by simp [source, outputCycle])
    (by
      dsimp only [source, outputCycle]
      exact odd_write_before_second_read configuration cycle)
    (by
      intro offset before
      dsimp only [outputCycle] at before
      simp only [secondOutputCycle_val] at before
      dsimp only [source]
      simp only [oddInputCycle_val]
      omega)
  have sourceWrite := bank0_write_at configuration execution start (by omega)
    writeSchedule source
  have targetSolution := execution.solution_at
    (start + halfFrameLength configuration + outputCycle.val) (by omega)
  have outputValue :=
    (outputHalves_of_solution targetSolution).2 lane
  have swap := readSwap_at configuration start within readSchedule outputCycle
  have swapTrue :
      ((hierarchy.get ⟨start + halfFrameLength configuration +
        outputCycle.val, by omega⟩).children .control).outputs
          .o_readSwap = true := by
    rw [swap]
    simp [outputCycle]
  rw [swapTrue] at outputValue
  have result :
      (hierarchy.get ⟨start + halfFrameLength configuration + outputCycle.val,
        by omega⟩).outputs .o_data (upperLane configuration lane) =
      (hierarchy.get ⟨start + source.val, by omega⟩).inputs
        .i_data (upperLane configuration lane) := by
    rw [outputValue, bankRead, sourceWrite.2.2]
    simp [source, oddInputCycle]
  simpa only [outputCycle, secondOutputCycle_val, source, oddInputCycle_val,
    ← full, two_mul, Nat.add_assoc] using result

private theorem second_lower_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + halfFrameLength configuration +
      configuration.frameLength ≤ hierarchy.length)
    (writeSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.writeObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
            .control).outputs = expectedWriteControls configuration cycle)
    (continuation : ∀ offset : Fin (halfFrameLength configuration),
      ∃ value : Nat, value ≤ offset.val ∧
        FinalReorder.Control.writeObservation (addressWidth configuration)
            ((hierarchy.get ⟨start + configuration.frameLength +
              offset.val, by omega⟩).children .control).outputs =
          FinalReorder.Control.writeControls (addressWidth configuration)
            (BitVector.ofNat (addressWidth configuration) value))
    (readSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.readObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + halfFrameLength configuration +
            cycle.val, by omega⟩).children .control).outputs =
        expectedReadControls configuration cycle)
    (cycle : Fin (halfFrameLength configuration))
    (lane : Fin (halfLaneCount configuration)) :
    (hierarchy.get ⟨start + configuration.frameLength + cycle.val,
      by
        have full := two_mul_halfFrameLength configuration
        omega⟩).outputs .o_data (lowerLane configuration lane) =
      (hierarchy.get ⟨start + (evenInputCycle configuration cycle).val,
        by
          have full := two_mul_halfFrameLength configuration
          omega⟩).inputs .i_data (upperLane configuration lane) := by
  have full := two_mul_halfFrameLength configuration
  let outputCycle := secondOutputCycle configuration cycle
  let source := evenInputCycle configuration cycle
  have bankRead := bank1_read_from_source configuration execution start within
    writeSchedule continuation readSchedule source outputCycle
    (by simp [source, outputCycle])
    (by
      dsimp only [source, outputCycle]
      exact even_write_before_second_read configuration cycle)
    (by
      intro offset before
      dsimp only [outputCycle] at before
      simp only [secondOutputCycle_val] at before
      dsimp only [source]
      simp only [evenInputCycle_val]
      omega)
  have sourceWrite := bank1_write_at configuration execution start (by omega)
    writeSchedule source
  have targetSolution := execution.solution_at
    (start + halfFrameLength configuration + outputCycle.val) (by omega)
  have outputValue :=
    (outputHalves_of_solution targetSolution).1 lane
  have swap := readSwap_at configuration start within readSchedule outputCycle
  have swapTrue :
      ((hierarchy.get ⟨start + halfFrameLength configuration +
        outputCycle.val, by omega⟩).children .control).outputs
          .o_readSwap = true := by
    rw [swap]
    simp [outputCycle]
  have bypassAtContinuation := continuationBypass_at configuration start
    (by omega) continuation cycle
  have bypassFalse :
      ((hierarchy.get ⟨start + halfFrameLength configuration +
        outputCycle.val, by omega⟩).children .control).outputs
          .o_bypass = false := by
    simp only [outputCycle, secondOutputCycle_val]
    simpa only [← full, two_mul, Nat.add_assoc] using bypassAtContinuation
  rw [swapTrue, bypassFalse] at outputValue
  have result :
      (hierarchy.get ⟨start + halfFrameLength configuration + outputCycle.val,
        by omega⟩).outputs .o_data (lowerLane configuration lane) =
      (hierarchy.get ⟨start + source.val, by omega⟩).inputs
        .i_data (upperLane configuration lane) := by
    rw [outputValue, bankRead, sourceWrite.2.2]
    simp [source, evenInputCycle]
  simpa only [outputCycle, secondOutputCycle_val, source, evenInputCycle_val,
    ← full, two_mul, Nat.add_assoc] using result

private theorem first_upper_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + halfFrameLength configuration +
      configuration.frameLength ≤ hierarchy.length)
    (writeSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.writeObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
            .control).outputs = expectedWriteControls configuration cycle)
    (continuation : ∀ offset : Fin (halfFrameLength configuration),
      ∃ value : Nat, value ≤ offset.val ∧
        FinalReorder.Control.writeObservation (addressWidth configuration)
            ((hierarchy.get ⟨start + configuration.frameLength +
              offset.val, by omega⟩).children .control).outputs =
          FinalReorder.Control.writeControls (addressWidth configuration)
            (BitVector.ofNat (addressWidth configuration) value))
    (readSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.readObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + halfFrameLength configuration +
            cycle.val, by omega⟩).children .control).outputs =
        expectedReadControls configuration cycle)
    (cycle : Fin (halfFrameLength configuration))
    (lane : Fin (halfLaneCount configuration)) :
    (hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
      by
        have full := two_mul_halfFrameLength configuration
        omega⟩).outputs .o_data (upperLane configuration lane) =
      (hierarchy.get ⟨start + (oddInputCycle configuration cycle).val,
        by
          have full := two_mul_halfFrameLength configuration
          omega⟩).inputs .i_data (lowerLane configuration lane) := by
  have full := two_mul_halfFrameLength configuration
  let outputCycle := firstOutputCycle configuration cycle
  let source := oddInputCycle configuration cycle
  let markedCycle := secondOutputCycle configuration cycle
  have targetSolution := execution.solution_at
    (start + halfFrameLength configuration + cycle.val) (by omega)
  have outputValue :=
    (outputHalves_of_solution targetSolution).2 lane
  have swap := readSwap_at configuration start within readSchedule outputCycle
  have swapFalse :
      ((hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
        by omega⟩).children .control).outputs .o_readSwap = false := by
    simp only [outputCycle, firstOutputCycle_val] at swap
    rw [swap]
    simp [Nat.not_le_of_gt cycle.isLt]
  have bypass := markedBypass_at configuration start (by omega)
    writeSchedule markedCycle
  have bypassAtTarget :
      ((hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
        by omega⟩).children .control).outputs .o_bypass =
          decide (cycle.val + 1 = halfFrameLength configuration) := by
    simp only [markedCycle, secondOutputCycle_val] at bypass
    have targetTime : start + (halfFrameLength configuration + cycle.val) =
        start + halfFrameLength configuration + cycle.val := by omega
    simp only [targetTime] at bypass
    rw [bypass]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  rw [swapFalse, bypassAtTarget] at outputValue
  by_cases last : cycle.val + 1 = halfFrameLength configuration
  · have sourceAtTarget : start + source.val =
        start + halfFrameLength configuration + cycle.val := by
      dsimp only [source]
      simp only [oddInputCycle_val]
      omega
    have sourceWrite := bank1_write_at configuration execution start (by omega)
      writeSchedule source
    have targetWiring := ModuleStructure.child_input targetSolution
      .bank1 .writeValue
    change ((hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
      by omega⟩).children .bank1).inputs .writeValue =
        ((hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
          by omega⟩).children .bank1Write).outputs .result at targetWiring
    have writeAtTarget :
        ((hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
          by omega⟩).children .bank1Write).outputs .result lane =
        (hierarchy.get ⟨start + source.val, by omega⟩).inputs
          .i_data (lowerLane configuration lane) := by
      have sourceValue :
          ((hierarchy.get ⟨start + source.val, by omega⟩).children
            .bank1).inputs .writeValue lane =
          (hierarchy.get ⟨start + source.val, by omega⟩).inputs
            .i_data (lowerLane configuration lane) := by
        have writeValue := congrFun sourceWrite.2.2 lane
        simpa [source, oddInputCycle] using writeValue
      have sourceValueAtTarget :
          ((hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
            by omega⟩).children .bank1).inputs .writeValue lane =
          (hierarchy.get ⟨start + source.val, by omega⟩).inputs
            .i_data (lowerLane configuration lane) := by
        simpa only [sourceAtTarget] using sourceValue
      exact (congrFun targetWiring lane).symm.trans sourceValueAtTarget
    rw [show decide (cycle.val + 1 = halfFrameLength configuration) = true by
      simp [last]] at outputValue
    simp at outputValue
    exact outputValue.trans writeAtTarget
  · have strictWrite : source.val <
        halfFrameLength configuration + outputCycle.val := by
      have le := odd_write_le_first_read configuration cycle
      have notEqual : source.val ≠
          halfFrameLength configuration + outputCycle.val := by
        intro equal
        have iff := odd_write_eq_first_read_iff configuration cycle
        apply last
        exact iff.mp (by simpa [source, outputCycle] using equal)
      omega
    have bankRead := bank1_read_from_source configuration execution start within
      writeSchedule continuation readSchedule source outputCycle
      (by simp [source, outputCycle]) strictWrite
      (by
        intro offset before
        change start + configuration.frameLength + offset.val <
          start + halfFrameLength configuration + cycle.val at before
        omega)
    have sourceWrite := bank1_write_at configuration execution start (by omega)
      writeSchedule source
    have bankRead' :
        ((hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
          by omega⟩).children .bank1).outputs (.readValue 0) =
        ((hierarchy.get ⟨start + source.val, by omega⟩).children
          .bank1).inputs .writeValue := by
      simpa only [outputCycle, firstOutputCycle_val] using bankRead
    rw [show decide (cycle.val + 1 = halfFrameLength configuration) = false by
      simp [last]] at outputValue
    simp at outputValue
    calc
      _ = ((hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
            by omega⟩).children .bank1).outputs (.readValue 0) lane :=
        outputValue
      _ = ((hierarchy.get ⟨start + source.val, by omega⟩).children
            .bank1).inputs .writeValue lane := congrFun bankRead' lane
      _ = _ := by
        have writeValue := congrFun sourceWrite.2.2 lane
        simpa [source, oddInputCycle] using writeValue

private theorem output_data_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + halfFrameLength configuration +
      configuration.frameLength ≤ hierarchy.length)
    (writeSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.writeObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + cycle.val, by omega⟩).children
            .control).outputs = expectedWriteControls configuration cycle)
    (continuation : ∀ offset : Fin (halfFrameLength configuration),
      ∃ value : Nat, value ≤ offset.val ∧
        FinalReorder.Control.writeObservation (addressWidth configuration)
            ((hierarchy.get ⟨start + configuration.frameLength +
              offset.val, by omega⟩).children .control).outputs =
          FinalReorder.Control.writeControls (addressWidth configuration)
            (BitVector.ofNat (addressWidth configuration) value))
    (readSchedule : ∀ cycle : Fin configuration.frameLength,
      FinalReorder.Control.readObservation (addressWidth configuration)
          ((hierarchy.get ⟨start + halfFrameLength configuration +
            cycle.val, by omega⟩).children .control).outputs =
        expectedReadControls configuration cycle)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    let inputFrame : OutputFrame configuration := fun frameCycle frameLane =>
      (hierarchy.get ⟨start + frameCycle.val, by
        have bound : frameCycle.val < configuration.frameLength := by
          simpa only [Configuration.finalGeometry_frameLength] using
            frameCycle.isLt
        omega⟩).inputs .i_data frameLane
    (hierarchy.get ⟨start + halfFrameLength configuration + cycle.val,
      by omega⟩).outputs .o_data lane =
        resultFrame configuration inputFrame cycle lane := by
  dsimp only
  have fullCycles := two_mul_halfFrameLength configuration
  have fullLanes := two_mul_halfLaneCount configuration
  let inputFrame : OutputFrame configuration := fun frameCycle frameLane =>
    (hierarchy.get ⟨start + frameCycle.val, by
      have bound : frameCycle.val < configuration.frameLength := by
        simpa only [Configuration.finalGeometry_frameLength] using
          frameCycle.isLt
      omega⟩).inputs .i_data frameLane
  by_cases firstHalf : cycle.val < halfFrameLength configuration
  · let halfCycle : Fin (halfFrameLength configuration) :=
      ⟨cycle.val, firstHalf⟩
    have cycleEqual : cycle = firstOutputCycle configuration halfCycle := by
      apply Fin.ext
      rfl
    by_cases lower : lane.val < halfLaneCount configuration
    · let halfLane : Fin (halfLaneCount configuration) := ⟨lane.val, lower⟩
      have laneEqual : lane = lowerLane configuration halfLane := by
        apply Fin.ext
        rfl
      have hardware := first_lower_at configuration execution start within
        writeSchedule continuation readSchedule halfCycle halfLane
      have semantic := first_lower configuration inputFrame halfCycle halfLane
      have result := hardware.trans (by
        symm
        simpa only [inputFrame, Configuration.finalGeometry_completed]
          using semantic)
      simpa only [cycleEqual, laneEqual, firstOutputCycle_val] using result
    · have upperBound : lane.val - halfLaneCount configuration <
          halfLaneCount configuration := by omega
      let halfLane : Fin (halfLaneCount configuration) :=
        ⟨lane.val - halfLaneCount configuration, upperBound⟩
      have laneEqual : lane = upperLane configuration halfLane := by
        apply Fin.ext
        dsimp only [halfLane, upperLane]
        omega
      have hardware := first_upper_at configuration execution start within
        writeSchedule continuation readSchedule halfCycle halfLane
      have semantic := first_upper configuration inputFrame halfCycle halfLane
      have result := hardware.trans (by
        symm
        simpa only [inputFrame, Configuration.finalGeometry_completed]
          using semantic)
      simpa only [cycleEqual, laneEqual, firstOutputCycle_val] using result
  · have secondBound : cycle.val - halfFrameLength configuration <
        halfFrameLength configuration := by omega
    let halfCycle : Fin (halfFrameLength configuration) :=
      ⟨cycle.val - halfFrameLength configuration, secondBound⟩
    have cycleEqual : cycle = secondOutputCycle configuration halfCycle := by
      apply Fin.ext
      dsimp only [halfCycle, secondOutputCycle]
      omega
    by_cases lower : lane.val < halfLaneCount configuration
    · let halfLane : Fin (halfLaneCount configuration) := ⟨lane.val, lower⟩
      have laneEqual : lane = lowerLane configuration halfLane := by
        apply Fin.ext
        rfl
      have hardware := second_lower_at configuration execution start within
        writeSchedule continuation readSchedule halfCycle halfLane
      have semantic := second_lower configuration inputFrame halfCycle halfLane
      have result := hardware.trans (by
        symm
        simpa only [inputFrame, Configuration.finalGeometry_completed]
          using semantic)
      simpa only [cycleEqual, laneEqual, secondOutputCycle_val,
        ← fullCycles, two_mul, Nat.add_assoc] using result
    · have upperBound : lane.val - halfLaneCount configuration <
          halfLaneCount configuration := by omega
      let halfLane : Fin (halfLaneCount configuration) :=
        ⟨lane.val - halfLaneCount configuration, upperBound⟩
      have laneEqual : lane = upperLane configuration halfLane := by
        apply Fin.ext
        dsimp only [halfLane, upperLane]
        omega
      have hardware := second_upper_at configuration execution start within
        writeSchedule continuation readSchedule halfCycle halfLane
      have semantic := second_upper configuration inputFrame halfCycle halfLane
      have result := hardware.trans (by
        symm
        simpa only [inputFrame, Configuration.finalGeometry_completed]
          using semantic)
      simpa only [cycleEqual, laneEqual, secondOutputCycle_val,
        ← fullCycles, two_mul, Nat.add_assoc] using result

private theorem output_starts
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {outputs : List (FinalReorder.ports configuration).outputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (hierarchyOutputs : hierarchy.map HierStep.outputs = outputs)
    (start : Nat)
    (inputWithin : start + configuration.frameLength ≤ inputs.length)
    (outputWithin : start + halfFrameLength configuration +
      configuration.frameLength ≤ outputs.length)
    (starts : FramedLatency.Starts configuration.frameLength_pos
      (fun input : (FinalReorder.ports configuration).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window inputs start inputWithin)) :
    FramedLatency.Starts configuration.frameLength_pos
      (fun output : (FinalReorder.ports configuration).outputs.Values =>
        (show Bool from output .o_first) = true)
      (FramedLatency.window outputs
        (start + halfFrameLength configuration) (by omega)) := by
  have hierarchyLength : hierarchy.length = outputs.length := by
    have equal := congrArg List.length hierarchyOutputs
    simpa only [List.length_map] using equal
  have markerAt (offset : Fin configuration.frameLength) :
      (FramedLatency.window outputs
        (start + halfFrameLength configuration) (by omega) offset) .o_first =
      (FramedLatency.window inputs start inputWithin offset) .i_first := by
    have sourceInHierarchy : start + offset.val < hierarchy.length := by
      rw [execution.length_eq]
      omega
    have targetInHierarchy : start + offset.val +
        halfFrameLength configuration < hierarchy.length := by
      rw [hierarchyLength]
      omega
    have sourceInInputs : start + offset.val < inputs.length := by omega
    have targetInOutputs : start + halfFrameLength configuration +
        offset.val < outputs.length := by omega
    have delayed := marker_delay_at configuration execution
      (start + offset.val) targetInHierarchy
    have parentInput := execution.input_at (start + offset.val)
      sourceInHierarchy sourceInInputs
    have parentOutput := execution.output_at hierarchyOutputs
      (start + halfFrameLength configuration + offset.val)
      (by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          targetInHierarchy)
      targetInOutputs
    rw [parentInput] at delayed
    have delayedFirst :
        (hierarchy.get ⟨start + halfFrameLength configuration + offset.val,
          by omega⟩).outputs .o_first =
        inputs.get ⟨start + offset.val, sourceInInputs⟩ .i_first := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using delayed.1
    rw [parentOutput] at delayedFirst
    simpa only [FramedLatency.window_apply] using delayedFirst
  constructor
  · change (FramedLatency.window outputs
      (start + halfFrameLength configuration) (by omega)
      ⟨0, configuration.frameLength_pos⟩) .o_first = true
    rw [markerAt]
    exact starts.first
  · intro offset nonzero marked
    apply starts.not_first offset nonzero
    change (FramedLatency.window outputs
      (start + halfFrameLength configuration) (by omega) offset) .o_first =
        true at marked
    rwa [markerAt] at marked

/-- The concrete two-bank hierarchy satisfies the natural final-reorder
frame contract, including a back-to-back following frame. -/
theorem contract_of_execution
    (depth : Nat) (configuration : Configuration depth)
    {initialState finalState :
      (FinalReorder.moduleStructure depth configuration).State}
    {inputs : List (FinalReorder.ports configuration).inputs.Values}
    {outputs : List (FinalReorder.ports configuration).outputs.Values}
    (execution : (FinalReorder.moduleStructure depth configuration).Executes
      initialState inputs outputs finalState) :
    FinalReorder.contract configuration execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, hierarchyOutputs⟩ := execution.observe
  unfold FinalReorder.contract FramedLatency.Holds FramedLatency.Relates
  rw [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  constructor
  · exact execution.length_eq
  · intro start inputWithin outputWithin starts
    have hierarchyLength : hierarchy.length = outputs.length := by
      have equal := congrArg List.length hierarchyOutputs
      simpa only [List.length_map] using equal
    have hierarchyWithin : start + halfFrameLength configuration +
        configuration.frameLength ≤ hierarchy.length := by
      rw [hierarchyLength]
      exact outputWithin
    have writeWithin : start + configuration.frameLength +
        halfFrameLength configuration ≤ inputs.length := by
      have lengths := execution.length_eq
      omega
    obtain ⟨writeSchedule, continuation⟩ :=
      control_write_schedule configuration observed start writeWithin starts
    have readSchedule := control_read_schedule configuration observed start
      (by omega) starts
    constructor
    · exact output_starts configuration observed hierarchyOutputs start
        inputWithin outputWithin starts
    · unfold FinalReorder.frameRelation FinalReorder.carriedRelation
      funext cycle lane
      have outputInHierarchy : start + halfFrameLength configuration +
          cycle.val < hierarchy.length := by omega
      have outputInOutputs : start + halfFrameLength configuration +
          cycle.val < outputs.length := by omega
      have outputBoundary := observed.output_at hierarchyOutputs
        (start + halfFrameLength configuration + cycle.val)
        outputInHierarchy outputInOutputs
      have physical := output_data_at configuration observed start
        hierarchyWithin writeSchedule continuation readSchedule cycle lane
      simp only [FramedLatency.window_apply, FinalReorder.inputObservation,
        FinalReorder.outputObservation]
      rw [← outputBoundary, physical]
      congr 2
      funext frameCycle frameLane
      have frameBound : frameCycle.val < configuration.frameLength := by
        simpa only [Configuration.finalGeometry_frameLength] using
          frameCycle.isLt
      have hierarchyIn : start + frameCycle.val < hierarchy.length := by
        rw [observed.length_eq]
        omega
      have inputIn : start + frameCycle.val < inputs.length := by omega
      have inputBoundary := observed.input_at (start + frameCycle.val)
        hierarchyIn inputIn
      rw [inputBoundary]

end HTFFT.Silean.FinalReorder.Internal
