import HTFFT.Silean.InitialReorder.Internal.InitialReorderPermutation
import HTFFT.Silean.InitialReorder.Internal.InitialReorderStep
import HTFFT.Silean.InitialReorder.Internal.InitialReorderStructural
import HTFFT.Silean.InitialReorder.Control.ControlFrame
import HTFFT.Silean.InitialReorder.BankLane.BankLaneTrace
import Silean.Semantics.StructuralObservation

/-! End-to-end certification of the concrete initial frame reorder. -/

namespace HTFFT.Silean.InitialReorder.Internal
open FFT

open _root_.Silean
open _root_.Silean.Modules

private abbrev reorderStructure (depth : Nat)
    (configuration : Configuration depth) :=
  InitialReorder.moduleStructure depth configuration

private abbrev ControlInput (configuration : Configuration depth) :=
  (InitialReorder.Control.ports
    (InitialReorder.addressWidth configuration)).inputs.Values

private abbrev ControlOutput (configuration : Configuration depth) :=
  (InitialReorder.Control.ports
    (InitialReorder.addressWidth configuration)).outputs.Values

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

@[simp] private theorem addressCardinality_eq_frameLength
    (configuration : Configuration depth) :
    BitVector.cardinality (InitialReorder.addressWidth configuration) =
      configuration.frameLength := by
  simp [BitVector.cardinality_eq_pow, InitialReorder.addressWidth,
    Configuration.frameLength]

private def controlCycle (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    Fin (BitVector.cardinality (InitialReorder.addressWidth configuration)) :=
  Fin.cast (addressCardinality_eq_frameLength configuration).symm cycle

@[simp] private theorem controlCycle_val (configuration : Configuration depth)
    (cycle : Fin configuration.frameLength) :
    (controlCycle configuration cycle).val = cycle.val :=
  rfl

private def addressCycle (configuration : Configuration depth)
    (address : Fin (InitialReorder.addressWidth configuration) → Bool) :
    Fin configuration.frameLength :=
  Fin.cast (addressCardinality_eq_frameLength configuration)
    (BitVector.toIndex (InitialReorder.addressWidth configuration) address)

@[simp] private theorem addressCycle_val (configuration : Configuration depth)
    (address : Fin (InitialReorder.addressWidth configuration) → Bool) :
    (addressCycle configuration address).val =
      BitVector.toNat (InitialReorder.addressWidth configuration) address :=
  by simp [addressCycle, BitVector.toIndex_val]

@[simp] private theorem cycleAddress_addressCycle
    (configuration : Configuration depth)
    (address : Fin (InitialReorder.addressWidth configuration) → Bool) :
    cycleAddress configuration (addressCycle configuration address) = address := by
  unfold cycleAddress addressCycle
  simp only [Fin.val_cast, BitVector.ofNat_toIndex]

/-- The controller schedule as seen inside one synchronized parent execution.
The first clause covers the marked write traversal; the second covers the
following read traversal even if later markers restart its address counter. -/
private theorem control_schedule
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start +
      BitVector.cardinality (InitialReorder.addressWidth configuration) +
      BitVector.cardinality (InitialReorder.addressWidth configuration) ≤
        inputs.length)
    (starts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos (InitialReorder.addressWidth configuration))
      (fun input : (InitialReorder.ports configuration).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window
        (length := BitVector.cardinality
          (InitialReorder.addressWidth configuration))
        inputs start (by omega))) :
    ∃ reversed : Bool,
      (List.ofFn (FramedLatency.window
        (length := BitVector.cardinality
          (InitialReorder.addressWidth configuration))
        (controlOutputs hierarchy) start (by
          have lengths := execution.length_eq
          simp only [controlOutputs, List.length_map]
          omega))).map
          (fun output => (output .o_address, output .o_reversed)) =
        InitialReorder.Control.expectedObservations
          (InitialReorder.addressWidth configuration) 0
          (BitVector.cardinality
            (InitialReorder.addressWidth configuration)) reversed ∧
      ∀ offset : Fin (BitVector.cardinality
          (InitialReorder.addressWidth configuration)),
        let observation := FramedLatency.window
          (length := BitVector.cardinality
            (InitialReorder.addressWidth configuration))
          (controlOutputs hierarchy)
          (start + BitVector.cardinality
            (InitialReorder.addressWidth configuration)) (by
            have lengths := execution.length_eq
            simp only [controlOutputs, List.length_map]
            omega) offset
        observation .o_reversed = !reversed ∧
          BitVector.toNat (InitialReorder.addressWidth configuration)
            (observation .o_address) ≤ offset.val := by
  let childExecution := execution.child (.control)
  have childContract := InitialReorder.Control.contract_of_execution
    (InitialReorder.addressWidth configuration) childExecution
  rcases childContract with ⟨controlInitial, controlFinal, controlTrace⟩
  rw [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
    at controlTrace
  change Trace
    (InitialReorder.Control.Transition
      (InitialReorder.addressWidth configuration))
    controlInitial (controlInputs hierarchy) (controlOutputs hierarchy)
    controlFinal at controlTrace
  have childWithin : start +
      BitVector.cardinality (InitialReorder.addressWidth configuration) +
      BitVector.cardinality (InitialReorder.addressWidth configuration) ≤
        (controlInputs hierarchy).length := by
    simp only [controlInputs, List.length_map]
    rw [execution.length_eq]
    exact within
  have childStarts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos (InitialReorder.addressWidth configuration))
      (fun input : ControlInput configuration =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window
        (length := BitVector.cardinality
          (InitialReorder.addressWidth configuration))
        (controlInputs hierarchy) start (by omega)) := by
    have childInputAt (offset : Fin (BitVector.cardinality
        (InitialReorder.addressWidth configuration))) :
        (FramedLatency.window (controlInputs hierarchy) start (by omega)
          offset) .i_first =
        (FramedLatency.window inputs start (by omega) offset) .i_first := by
      have hierarchyIn : start + offset.val < hierarchy.length := by
        rw [execution.length_eq]
        omega
      have inputIn : start + offset.val < inputs.length := by omega
      have solution := execution.solution_at
        (start + offset.val) hierarchyIn
      have wired := controlInput_of_solution solution
      have parentInput := execution.input_at
        (start + offset.val) hierarchyIn inputIn
      rw [parentInput] at wired
      simpa only [FramedLatency.window_apply, controlInputs,
        List.get_eq_getElem, List.getElem_map] using wired
    constructor
    · change (FramedLatency.window (controlInputs hierarchy) start (by omega)
          ⟨0, by
            rw [BitVector.cardinality_eq_pow]
            exact Nat.two_pow_pos
              (InitialReorder.addressWidth configuration)⟩) .i_first = true
      rw [childInputAt]
      exact starts.first
    · intro offset nonzero marked
      apply starts.not_first offset nonzero
      change (FramedLatency.window (controlInputs hierarchy) start (by omega)
          offset) .i_first = true at marked
      rwa [childInputAt] at marked
  exact InitialReorder.Control.observations_of_marked_window_with_continuation
    (InitialReorder.addressWidth_pos configuration) controlTrace start
    childWithin childStarts

/-- Pointwise form of `control_schedule` indexed by the FFT frame cycle
rather than the controller's cardinality type. -/
private theorem control_schedule_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + configuration.frameLength +
      configuration.frameLength ≤ inputs.length)
    (starts : FramedLatency.Starts configuration.frameLength_pos
      (fun input : (InitialReorder.ports configuration).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window inputs start (by omega))) :
    ∃ reversed : Bool,
      (∀ cycle : Fin configuration.frameLength,
        let observation := ((hierarchy.get ⟨start + cycle.val, by
          rw [execution.length_eq]
          omega⟩).children .control).outputs
        observation .o_address = cycleAddress configuration cycle ∧
          observation .o_reversed = reversed) ∧
      (∀ offset : Fin configuration.frameLength,
        let observation := ((hierarchy.get
          ⟨start + configuration.frameLength + offset.val, by
            rw [execution.length_eq]
            omega⟩).children .control).outputs
        observation .o_reversed = !reversed ∧
          BitVector.toNat (InitialReorder.addressWidth configuration)
            (observation .o_address) ≤ offset.val) := by
  have controlWithin : start +
      BitVector.cardinality (InitialReorder.addressWidth configuration) +
      BitVector.cardinality (InitialReorder.addressWidth configuration) ≤
        inputs.length := by
    simpa only [addressCardinality_eq_frameLength] using within
  have controlStarts : FramedLatency.Starts
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos (InitialReorder.addressWidth configuration))
      (fun input : (InitialReorder.ports configuration).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window
        (length := BitVector.cardinality
          (InitialReorder.addressWidth configuration))
        inputs start (by omega)) := by
    exact FramedLatency.starts_window_of_length_eq
      (addressCardinality_eq_frameLength configuration).symm
      inputs start (by omega) (by omega) configuration.frameLength_pos
      (by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos (InitialReorder.addressWidth configuration))
      (fun input : (InitialReorder.ports configuration).inputs.Values =>
        (show Bool from input .i_first) = true) starts
  obtain ⟨reversed, firstSchedule, continuation⟩ :=
    control_schedule configuration execution start controlWithin controlStarts
  refine ⟨reversed, ?_, ?_⟩
  · intro cycle
    have leftOccurs : (controlCycle configuration cycle).val <
        ((List.ofFn (FramedLatency.window
          (length := BitVector.cardinality
            (InitialReorder.addressWidth configuration))
          (controlOutputs hierarchy) start (by
            have lengths := execution.length_eq
            simp only [controlOutputs, List.length_map]
            omega))).map
              (fun output => (output .o_address, output .o_reversed))).length := by
      simp
    have rightOccurs : (controlCycle configuration cycle).val <
        (InitialReorder.Control.expectedObservations
          (InitialReorder.addressWidth configuration) 0
          (BitVector.cardinality
            (InitialReorder.addressWidth configuration)) reversed).length := by
      simp [InitialReorder.Control.expectedObservations]
    have atValue := congrArg (fun values =>
      values[(controlCycle configuration cycle).val]?) firstSchedule
    have someValues :=
      (List.getElem?_eq_getElem leftOccurs).symm.trans
        (atValue.trans (List.getElem?_eq_getElem rightOccurs))
    have atValue := Option.some.inj someValues
    constructor
    · simpa [InitialReorder.Control.expectedObservations, cycleAddress,
        List.get_eq_getElem, FramedLatency.window, controlOutputs,
        List.getElem_map] using congrArg Prod.fst atValue
    · simpa [InitialReorder.Control.expectedObservations,
        List.get_eq_getElem, FramedLatency.window, controlOutputs,
        List.getElem_map] using congrArg Prod.snd atValue
  · intro offset
    simpa [FramedLatency.window, controlOutputs, List.get_eq_getElem,
      List.getElem_map, controlCycle_val,
      addressCardinality_eq_frameLength] using
      continuation (controlCycle configuration offset)

/-- The dedicated marker delay transports the valid-frame marker to the
parent output boundary. -/
private theorem output_starts
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {outputs : List (InitialReorder.ports configuration).outputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (hierarchyOutputs : hierarchy.map HierStep.outputs = outputs)
    (start : Nat)
    (inputWithin : start + configuration.frameLength ≤ inputs.length)
    (outputWithin : start + configuration.initialReorderLatency +
      configuration.frameLength ≤ outputs.length)
    (starts : FramedLatency.Starts configuration.frameLength_pos
      (fun input : (InitialReorder.ports configuration).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window inputs start inputWithin)) :
    FramedLatency.Starts configuration.frameLength_pos
      (fun output : (InitialReorder.ports configuration).outputs.Values =>
        (show Bool from output .o_first) = true)
      (FramedLatency.window outputs
        (start + configuration.initialReorderLatency) (by omega)) := by
  let markerExecution := execution.child (.markerAlign)
  have markerContract := ShiftRegister.contract_of_execution .bit
    configuration.initialReorderLatency
    (InitialReorder.Internal.markerLatency_pos configuration) markerExecution
  have markerAt (offset : Fin configuration.frameLength) :
      (FramedLatency.window outputs
        (start + configuration.initialReorderLatency) (by omega) offset)
          .o_first =
        (FramedLatency.window inputs start inputWithin offset) .i_first := by
    have hierarchyLength := execution.length_eq
    have sourceInHierarchy : start + offset.val < hierarchy.length := by
      rw [hierarchyLength]
      omega
    have targetInHierarchy : start + configuration.initialReorderLatency +
        offset.val < hierarchy.length := by
      have lengths := congrArg List.length hierarchyOutputs
      simp only [List.length_map] at lengths
      rw [lengths]
      omega
    have sourceInInputs : start + offset.val < inputs.length := by omega
    have targetInOutputs : start + configuration.initialReorderLatency +
        offset.val < outputs.length := by omega
    have delayed := FixedLatency.relation_at_of_trace markerExecution
      markerContract (start + offset.val) (by
        simp only [List.length_map]
        exact sourceInHierarchy) (by
          simp only [List.length_map]
          omega)
    change (show Bool from
        ((hierarchy.map fun step =>
          (step.children .markerAlign).outputs).get
            ⟨start + offset.val + configuration.initialReorderLatency,
              by simp only [List.length_map]; omega⟩) .output) =
      (show Bool from
        ((hierarchy.map fun step =>
          (step.children .markerAlign).inputs).get
            ⟨start + offset.val,
              by simp only [List.length_map]; exact sourceInHierarchy⟩) .input)
      at delayed
    have sourceSolution := execution.solution_at
      (start + offset.val) sourceInHierarchy
    have targetSolution := execution.solution_at
      (start + configuration.initialReorderLatency + offset.val)
      targetInHierarchy
    have sourceWiring := markerWiring_of_solution sourceSolution
    have targetWiring := markerWiring_of_solution targetSolution
    have parentInput := execution.input_at (start + offset.val)
      sourceInHierarchy sourceInInputs
    have parentOutput := execution.output_at hierarchyOutputs
      (start + configuration.initialReorderLatency + offset.val)
      targetInHierarchy targetInOutputs
    rw [parentInput] at sourceWiring
    rw [parentOutput] at targetWiring
    simp only [FramedLatency.window_apply]
    rw [targetWiring.2]
    calc
      (show Bool from ((hierarchy.get
          ⟨start + configuration.initialReorderLatency + offset.val,
            targetInHierarchy⟩).children .markerAlign).outputs .output) =
          (show Bool from ((hierarchy.get
            ⟨start + offset.val, sourceInHierarchy⟩).children
              .markerAlign).inputs .input) := by
        simpa only [List.get_eq_getElem, List.getElem_map, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using delayed
      _ = _ := sourceWiring.1
  constructor
  · change (FramedLatency.window outputs
      (start + configuration.initialReorderLatency) (by omega)
        ⟨0, configuration.frameLength_pos⟩) .o_first = true
    rw [markerAt]
    exact starts.first
  · intro offset nonzero marked
    apply starts.not_first offset nonzero
    change (FramedLatency.window outputs
      (start + configuration.initialReorderLatency) (by omega) offset)
        .o_first = true at marked
    rwa [markerAt] at marked

/-- Evaluate the write-side barrel pipeline at one absolute source cycle. -/
private theorem preBarrel_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (time : Nat)
    (targetIn : time + barrelLatency configuration < hierarchy.length) :
    ((hierarchy.get ⟨time + barrelLatency configuration, targetIn⟩).children
        .preBarrel).outputs .result =
      BarrelShifter.resultValue configuration.laneDepth
        (InitialReorder.preRotation configuration
          (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_address))
        (fun lane => InitialReorder.Lane.resultValue configuration lane
          ((hierarchy.get ⟨time, by omega⟩).inputs .i_data lane)
          (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_address)
          (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_reversed)) := by
  let childExecution := execution.child (.preBarrel)
  have childContract := BarrelShifter.contract_of_execution
    (payloadType configuration) configuration.laneDepth
    configuration.initialBarrelPipeline childExecution
  have related := FixedLatency.relation_at_of_trace childExecution
    childContract time (by simp only [List.length_map]; omega) (by
      simp only [List.length_map]
      exact targetIn)
  have sourceSolution := execution.solution_at time (by omega)
  have inputsEqual := writeBarrelInputs_of_solution sourceSolution
  change ((hierarchy.map fun step :
      HierStep (reorderStructure depth configuration) =>
      (step.children .preBarrel).outputs).get
        ⟨time + barrelLatency configuration, by
          simp only [List.length_map]
          exact targetIn⟩) .result =
    BarrelShifter.resultValue configuration.laneDepth
      (((hierarchy.map fun step :
        HierStep (reorderStructure depth configuration) =>
        (step.children .preBarrel).inputs).get
          ⟨time, by simp only [List.length_map]; omega⟩) .shift)
      (((hierarchy.map fun step :
        HierStep (reorderStructure depth configuration) =>
        (step.children .preBarrel).inputs).get
          ⟨time, by simp only [List.length_map]; omega⟩) .data) at related
  have related' := related
  simp only [List.get_eq_getElem, List.getElem_map] at related'
  calc
    _ = BarrelShifter.resultValue configuration.laneDepth
        (show Fin configuration.laneDepth → Bool from
          ((hierarchy.get ⟨time, by omega⟩).children .preBarrel).inputs
            .shift)
        (show Fin configuration.laneCount →
            (payloadType configuration).Denote from
          ((hierarchy.get ⟨time, by omega⟩).children .preBarrel).inputs
            .data) := related'
    _ = _ := congrArg₂
      (BarrelShifter.resultValue configuration.laneDepth)
      inputsEqual.1 inputsEqual.2

/-- The independent read-control paths reproduce one controller coordinate
one complete frame later. -/
private theorem readAlign_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (time : Nat)
    (targetIn : time + configuration.frameLength < hierarchy.length) :
    ((hierarchy.get ⟨time + configuration.frameLength, targetIn⟩).children
        .readCycleAlign).outputs .output =
        ((hierarchy.get ⟨time, by omega⟩).children .control).outputs
          .o_address ∧
      ((hierarchy.get ⟨time + configuration.frameLength, targetIn⟩).children
        .readOrientationAlign).outputs .output =
        ((hierarchy.get ⟨time, by omega⟩).children .control).outputs
          .o_reversed ∧
      ((hierarchy.get ⟨time + configuration.frameLength, targetIn⟩).children
        .readRotationAlign).outputs .output =
        InitialReorder.laneRotation configuration
          (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_address) := by
  have sourceSolution := execution.solution_at time (by omega)
  have sourceInputs := readAlignInputs_of_solution sourceSolution
  have cycleExecution := execution.child (.readCycleAlign)
  have cycleContract := ShiftRegister.contract_of_execution
    (.vector (InitialReorder.addressWidth configuration) .bit)
    configuration.frameLength configuration.frameLength_pos cycleExecution
  have cycleDelayed := FixedLatency.relation_at_of_trace cycleExecution
    cycleContract time (by simp only [List.length_map]; omega) (by
      simp only [List.length_map]
      exact targetIn)
  have orientationExecution := execution.child (.readOrientationAlign)
  have orientationContract := ShiftRegister.contract_of_execution .bit
    configuration.frameLength configuration.frameLength_pos
    orientationExecution
  have orientationDelayed := FixedLatency.relation_at_of_trace
    orientationExecution orientationContract time
    (by simp only [List.length_map]; omega) (by
      simp only [List.length_map]
      exact targetIn)
  have rotationExecution := execution.child (.readRotationAlign)
  have rotationContract := ShiftRegister.contract_of_execution
    (.vector configuration.laneDepth .bit)
    configuration.frameLength configuration.frameLength_pos rotationExecution
  have rotationDelayed := FixedLatency.relation_at_of_trace rotationExecution
    rotationContract time (by simp only [List.length_map]; omega) (by
      simp only [List.length_map]
      exact targetIn)
  simp only [List.get_eq_getElem, List.getElem_map] at cycleDelayed
  simp only [List.get_eq_getElem, List.getElem_map] at orientationDelayed
  simp only [List.get_eq_getElem, List.getElem_map] at rotationDelayed
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = (show Fin (InitialReorder.addressWidth configuration) → Bool from
          ((hierarchy.get ⟨time, by omega⟩).children
            .readCycleAlign).inputs .input) := cycleDelayed
      _ = _ := sourceInputs.1
  · calc
      _ = (show Bool from ((hierarchy.get ⟨time, by omega⟩).children
          .readOrientationAlign).inputs .input) := orientationDelayed
      _ = _ := sourceInputs.2.1
  · calc
      _ = (show Fin configuration.laneDepth → Bool from
          ((hierarchy.get ⟨time, by omega⟩).children
            .readRotationAlign).inputs .input) := rotationDelayed
      _ = _ := sourceInputs.2.2

/-- Evaluate the delayed read-address barrel pipeline from one controller
coordinate. -/
private theorem readPreBarrel_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (time : Nat)
    (targetIn : time + configuration.frameLength +
      barrelLatency configuration < hierarchy.length) :
    ((hierarchy.get ⟨time + configuration.frameLength +
        barrelLatency configuration, targetIn⟩).children
        .readPreBarrel).outputs .result =
      BarrelShifter.resultValue configuration.laneDepth
        (InitialReorder.preRotation configuration
          (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_address))
        (fun lane => InitialReorder.Lane.memoryAddress configuration lane
          (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_address)
          (!(((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_reversed))) := by
  have aligned := readAlign_at configuration execution time (by omega)
  have delayedSolution := execution.solution_at
    (time + configuration.frameLength) (by omega)
  have inputsEqual := readBarrelInputs_of_solution delayedSolution
  have shiftEqual :
      ((hierarchy.get ⟨time + configuration.frameLength, by omega⟩).children
        .readPreBarrel).inputs .shift =
        InitialReorder.preRotation configuration
          (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_address) := by
    rw [inputsEqual.1, aligned.2.2]
    rfl
  have dataEqual :
      ((hierarchy.get ⟨time + configuration.frameLength, by omega⟩).children
        .readPreBarrel).inputs .data =
        fun lane => InitialReorder.Lane.memoryAddress configuration lane
          (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_address)
          (!(((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_reversed)) := by
    rw [inputsEqual.2, aligned.1, aligned.2.1]
  let childExecution := execution.child (.readPreBarrel)
  have childContract := BarrelShifter.contract_of_execution
    (.vector (InitialReorder.addressWidth configuration) .bit)
    configuration.laneDepth configuration.initialBarrelPipeline childExecution
  have related := FixedLatency.relation_at_of_trace childExecution
    childContract (time + configuration.frameLength)
    (by simp only [List.length_map]; omega) (by
      simp only [List.length_map]
      simpa only [Nat.add_assoc] using targetIn)
  simp only [List.get_eq_getElem, List.getElem_map] at related
  calc
    _ = BarrelShifter.resultValue configuration.laneDepth
        (show Fin configuration.laneDepth → Bool from
          ((hierarchy.get ⟨time + configuration.frameLength, by omega⟩).children
            .readPreBarrel).inputs .shift)
        (show Fin configuration.laneCount →
            (Fin (InitialReorder.addressWidth configuration) → Bool) from
          ((hierarchy.get ⟨time + configuration.frameLength, by omega⟩).children
            .readPreBarrel).inputs .data) := related
    _ = _ := congrArg₂
      (BarrelShifter.resultValue configuration.laneDepth)
      shiftEqual dataEqual

/-- The post-barrel rotation is delayed to the registered bank-output cycle. -/
private theorem postRotation_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (time : Nat)
    (targetIn : (time + configuration.frameLength) +
      (barrelLatency configuration + 1) < hierarchy.length) :
    ((hierarchy.get ⟨(time + configuration.frameLength) +
        (barrelLatency configuration + 1), targetIn⟩).children
        .postRotationAlign).outputs .output =
      InitialReorder.laneRotation configuration
        (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
          .o_address) := by
  have aligned := readAlign_at configuration execution time (by omega)
  have alignedSolution := execution.solution_at
    (time + configuration.frameLength) (by omega)
  have postInput := postRotationInput_of_solution alignedSolution
  have inputEqual :
      ((hierarchy.get ⟨time + configuration.frameLength, by omega⟩).children
        .postRotationAlign).inputs .input =
      InitialReorder.laneRotation configuration
        (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
          .o_address) := postInput.trans aligned.2.2
  let childExecution := execution.child (.postRotationAlign)
  have childContract := OptionalShiftRegister.contract_of_execution
    (.vector configuration.laneDepth .bit)
    (barrelLatency configuration + 1) childExecution
  have related := FixedLatency.relation_at_of_trace childExecution
    childContract (time + configuration.frameLength)
    (by simp only [List.length_map]; omega) (by
      simp only [List.length_map]
      simpa only [Nat.add_assoc] using targetIn)
  change (show Fin configuration.laneDepth → Bool from
      ((hierarchy.map fun step :
        HierStep (reorderStructure depth configuration) =>
        (step.children .postRotationAlign).outputs).get
          ⟨(time + configuration.frameLength) +
              (barrelLatency configuration + 1),
            by
              simp only [List.length_map]
              simpa only [Nat.add_assoc] using targetIn⟩) .output) =
    (show Fin configuration.laneDepth → Bool from
      ((hierarchy.map fun step :
        HierStep (reorderStructure depth configuration) =>
        (step.children .postRotationAlign).inputs).get
          ⟨time + configuration.frameLength,
            by simp only [List.length_map]; omega⟩) .input) at related
  simp only [List.get_eq_getElem, List.getElem_map] at related
  calc
    _ = (show Fin configuration.laneDepth → Bool from
        ((hierarchy.get ⟨time + configuration.frameLength, by omega⟩).children
          .postRotationAlign).inputs .input) := by
      exact related
    _ = _ := inputEqual

/-- Evaluate the final barrel pipeline and parent data wiring at one source
cycle. -/
private theorem postBarrel_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (time : Nat)
    (targetIn : time + barrelLatency configuration < hierarchy.length) :
    (hierarchy.get ⟨time + barrelLatency configuration, targetIn⟩).outputs
        .o_data =
      BarrelShifter.resultValue configuration.laneDepth
        (((hierarchy.get ⟨time, by omega⟩).children
          .postRotationAlign).outputs .output)
        (fun lane => ((hierarchy.get ⟨time, by omega⟩).children
          (.bank lane)).outputs .o_data) := by
  have sourceSolution := execution.solution_at time (by omega)
  have sourceInputs := postBarrelInputs_of_solution sourceSolution
  have targetSolution := execution.solution_at
    (time + barrelLatency configuration) targetIn
  have targetOutput := dataOutput_of_solution targetSolution
  let childExecution := execution.child (.postBarrel)
  have childContract := BarrelShifter.contract_of_execution
    (sampleType configuration) configuration.laneDepth
    configuration.initialBarrelPipeline childExecution
  have related := FixedLatency.relation_at_of_trace childExecution
    childContract time (by simp only [List.length_map]; omega) (by
      simp only [List.length_map]
      exact targetIn)
  simp only [List.get_eq_getElem, List.getElem_map] at related
  rw [targetOutput]
  calc
    _ = BarrelShifter.resultValue configuration.laneDepth
        (show Fin configuration.laneDepth → Bool from
          ((hierarchy.get ⟨time, by omega⟩).children
            .postBarrel).inputs .shift)
        (show Fin configuration.laneCount →
            (sampleType configuration).Denote from
          ((hierarchy.get ⟨time, by omega⟩).children
            .postBarrel).inputs .data) := related
    _ = _ := congrArg₂
      (BarrelShifter.resultValue configuration.laneDepth)
      sourceInputs.1 sourceInputs.2

/-- The payload written to a chosen bank is the source lane selected by the
negative pre-rotation. -/
private theorem bankWrite_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (time : Nat) (bank : Fin configuration.laneCount)
    (targetIn : time + barrelLatency configuration < hierarchy.length) :
    ((hierarchy.get ⟨time + barrelLatency configuration, targetIn⟩).children
      (.bank bank)).inputs .i_writePayload =
      let lane := BarrelShifter.sourceIndex configuration.laneDepth
        (InitialReorder.preRotation configuration
          (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_address)) bank
      InitialReorder.Lane.resultValue configuration lane
        ((hierarchy.get ⟨time, by omega⟩).inputs .i_data lane)
        (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
          .o_address)
        (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
          .o_reversed) := by
  have prepared := preBarrel_at configuration execution time targetIn
  have targetSolution := execution.solution_at
    (time + barrelLatency configuration) targetIn
  have bankInputs := bankInputs_of_solution targetSolution bank
  rw [bankInputs.1, prepared]
  rfl

/-- The read address presented to a chosen bank is selected by the matching
delayed negative rotation and uses the opposite orientation. -/
private theorem bankRead_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (time : Nat) (bank : Fin configuration.laneCount)
    (targetIn : time + configuration.frameLength +
      barrelLatency configuration < hierarchy.length) :
    ((hierarchy.get ⟨time + configuration.frameLength +
      barrelLatency configuration, targetIn⟩).children
      (.bank bank)).inputs .i_readAddress =
      let lane := BarrelShifter.sourceIndex configuration.laneDepth
        (InitialReorder.preRotation configuration
          (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
            .o_address)) bank
      InitialReorder.Lane.memoryAddress configuration lane
        (((hierarchy.get ⟨time, by omega⟩).children .control).outputs
          .o_address)
        (!(((hierarchy.get ⟨time, by omega⟩).children .control).outputs
          .o_reversed)) := by
  have prepared := readPreBarrel_at configuration execution time targetIn
  have targetSolution := execution.solution_at
    (time + configuration.frameLength + barrelLatency configuration) targetIn
  have bankInputs := bankInputs_of_solution targetSolution bank
  rw [bankInputs.2, prepared]
  rfl

/-- Between the selected write and its later read, the same bank is never
written at the selected local address. -/
private theorem bank_not_overwritten
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat) (reversed : Bool)
    (controlWithin : start + configuration.frameLength +
      configuration.frameLength ≤ hierarchy.length)
    (firstSchedule : ∀ cycle : Fin configuration.frameLength,
      let observation := ((hierarchy.get ⟨start + cycle.val, by
        omega⟩).children .control).outputs
      observation .o_address = cycleAddress configuration cycle ∧
        observation .o_reversed = reversed)
    (continuation : ∀ offset : Fin configuration.frameLength,
      let observation := ((hierarchy.get
        ⟨start + configuration.frameLength + offset.val, by
          omega⟩).children .control).outputs
      observation .o_reversed = !reversed ∧
        BitVector.toNat (InitialReorder.addressWidth configuration)
          (observation .o_address) ≤ offset.val)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount)
    (readIn : start + configuration.frameLength + cycle.val +
      barrelLatency configuration < hierarchy.length)
    (position : Nat)
    (afterWrite : start +
      (reversedCycle configuration cycle lane).val +
      barrelLatency configuration < position)
    (beforeRead : position < start + configuration.frameLength + cycle.val +
      barrelLatency configuration) :
    InitialReorder.BankLane.writeIndex configuration
        ((hierarchy.map fun step =>
          (step.children (.bank (bankIndex configuration cycle lane))).inputs
        ).get ⟨position, by simp only [List.length_map]; omega⟩) ≠
      InitialReorder.BankLane.writeIndex configuration
        ((hierarchy.map fun step =>
          (step.children (.bank (bankIndex configuration cycle lane))).inputs
        ).get ⟨start + (reversedCycle configuration cycle lane).val +
          barrelLatency configuration, by
            simp only [List.length_map]
            omega⟩) := by
  intro equalIndex
  let sourceCycle := reversedCycle configuration cycle lane
  let sourceLane := reversedLane configuration cycle lane
  let bank := bankIndex configuration cycle lane
  let sourceTime := position - barrelLatency configuration
  have writeSourceIn : start + sourceCycle.val +
      barrelLatency configuration < hierarchy.length := by omega
  have sourceTimeRestore : sourceTime + barrelLatency configuration =
      position := by
    dsimp only [sourceTime]
    omega
  have sourceTimeAfter : start + sourceCycle.val < sourceTime := by
    dsimp only [sourceTime]
    omega
  have sourceTimeBefore : sourceTime <
      start + configuration.frameLength + cycle.val := by
    dsimp only [sourceTime]
    omega
  have sourceTimeIn : sourceTime + barrelLatency configuration <
      hierarchy.length := by omega
  have targetWrite := bankWrite_at configuration execution
    (start + sourceCycle.val) bank writeSourceIn
  have sourceControl := firstSchedule sourceCycle
  have reversedBank : bankIndex configuration sourceCycle sourceLane = bank := by
    exact bankIndex_reversed configuration cycle lane
  rw [sourceControl.1, sourceControl.2] at targetWrite
  rw [← reversedBank,
    preRotation_sourceIndex configuration sourceCycle sourceLane] at targetWrite
  have targetWriteBank :
      ((hierarchy.get ⟨start + sourceCycle.val +
        barrelLatency configuration, writeSourceIn⟩).children
          (.bank bank)).inputs .i_writePayload =
        InitialReorder.Lane.resultValue configuration sourceLane
          ((hierarchy.get ⟨start + sourceCycle.val, by omega⟩).inputs
            .i_data sourceLane)
          (cycleAddress configuration sourceCycle) reversed := by
    rw [reversedBank] at targetWrite
    exact targetWrite
  have intermediateWriteRaw := bankWrite_at configuration execution
    sourceTime bank sourceTimeIn
  have intermediateWrite :
      ((hierarchy.get ⟨position, by omega⟩).children (.bank bank)).inputs
          .i_writePayload =
        let selected := BarrelShifter.sourceIndex configuration.laneDepth
          (InitialReorder.preRotation configuration
            (((hierarchy.get ⟨sourceTime, by omega⟩).children
              .control).outputs .o_address)) bank
        InitialReorder.Lane.resultValue configuration selected
          ((hierarchy.get ⟨sourceTime, by omega⟩).inputs .i_data selected)
          (((hierarchy.get ⟨sourceTime, by omega⟩).children
            .control).outputs .o_address)
          (((hierarchy.get ⟨sourceTime, by omega⟩).children
            .control).outputs .o_reversed) := by
    simpa only [List.get_eq_getElem, sourceTimeRestore] using
      intermediateWriteRaw
  have indexEqual :
      InitialReorder.BankLane.writeIndex configuration
          ((hierarchy.get ⟨position, by omega⟩).children (.bank bank)).inputs =
        InitialReorder.BankLane.writeIndex configuration
          ((hierarchy.get ⟨start + sourceCycle.val +
            barrelLatency configuration, by omega⟩).children
              (.bank bank)).inputs := by
    simpa only [List.get_eq_getElem, List.getElem_map, bank, sourceCycle]
      using equalIndex
  by_cases inFirst : sourceTime < start + configuration.frameLength
  · let currentCycle : Fin configuration.frameLength :=
      ⟨sourceTime - start, by omega⟩
    have currentControl := firstSchedule currentCycle
    have currentTime : start + currentCycle.val = sourceTime := by
      dsimp only [currentCycle]
      omega
    have currentAddress :
        ((hierarchy.get ⟨sourceTime, by omega⟩).children
          .control).outputs .o_address =
          cycleAddress configuration currentCycle := by
      simpa only [List.get_eq_getElem, currentTime] using currentControl.1
    have currentReversed :
        ((hierarchy.get ⟨sourceTime, by omega⟩).children
          .control).outputs .o_reversed = reversed := by
      simpa only [List.get_eq_getElem, currentTime] using currentControl.2
    let selected := BarrelShifter.sourceIndex configuration.laneDepth
      (InitialReorder.preRotation configuration
        (cycleAddress configuration currentCycle)) bank
    rw [currentAddress, currentReversed] at intermediateWrite
    have addressEqual :
        InitialReorder.Lane.memoryAddress configuration selected
            (cycleAddress configuration currentCycle) reversed =
          InitialReorder.Lane.memoryAddress configuration sourceLane
            (cycleAddress configuration sourceCycle) reversed := by
      unfold InitialReorder.BankLane.writeIndex at indexEqual
      rw [intermediateWrite, targetWriteBank] at indexEqual
      have numeric := congrArg Fin.val indexEqual
      simp only [InitialReorder.BankLane.payloadAddress,
        InitialReorder.BankLane.payloadFields,
        InitialReorder.Lane.resultValue_address,
        BitVector.toIndex_val] at numeric
      exact BitVector.toNat_injective _ numeric
    have bankEqual : bankIndex configuration currentCycle selected =
        bankIndex configuration sourceCycle sourceLane := by
      calc
        _ = bank := by
          dsimp only [selected]
          rw [bankIndex_preRotation_source]
        _ = _ := reversedBank.symm
    have coordinateEqual := bankAddress_injective configuration reversed
      bankEqual addressEqual
    have valueEqual := congrArg Fin.val coordinateEqual.1
    dsimp only [currentCycle, sourceCycle] at valueEqual sourceTimeAfter
    omega
  · have afterFrame : start + configuration.frameLength ≤ sourceTime := by omega
    let offset : Fin configuration.frameLength :=
      ⟨sourceTime - (start + configuration.frameLength), by omega⟩
    have currentControl := continuation offset
    let address : Fin (InitialReorder.addressWidth configuration) → Bool :=
      ((hierarchy.get
      ⟨start + configuration.frameLength + offset.val, by
        omega⟩).children .control).outputs .o_address
    let currentCycle := addressCycle configuration address
    let selected := BarrelShifter.sourceIndex configuration.laneDepth
      (InitialReorder.preRotation configuration address) bank
    have sourceTimeEqual :
        start + configuration.frameLength + offset.val = sourceTime := by
      dsimp only [offset]
      omega
    have addressAt :
        ((hierarchy.get ⟨sourceTime, by omega⟩).children .control).outputs
            .o_address = address := by
      dsimp only [address]
      simp only [List.get_eq_getElem, sourceTimeEqual]
    have reversedAt :
        ((hierarchy.get ⟨sourceTime, by omega⟩).children .control).outputs
            .o_reversed = !reversed := by
      simpa only [List.get_eq_getElem, sourceTimeEqual] using currentControl.1
    rw [addressAt, reversedAt] at intermediateWrite
    have targetAddress :
        InitialReorder.Lane.memoryAddress configuration sourceLane
            (cycleAddress configuration sourceCycle) reversed =
          InitialReorder.Lane.memoryAddress configuration lane
            (cycleAddress configuration cycle) (!reversed) := by
      simpa only [Bool.not_not] using
        memoryAddress_opposite configuration cycle lane (!reversed)
    have addressEqual :
        InitialReorder.Lane.memoryAddress configuration selected
            (cycleAddress configuration currentCycle) (!reversed) =
          InitialReorder.Lane.memoryAddress configuration lane
            (cycleAddress configuration cycle) (!reversed) := by
      have writeAddressEqual :
          InitialReorder.Lane.memoryAddress configuration selected address
              (!reversed) =
            InitialReorder.Lane.memoryAddress configuration sourceLane
              (cycleAddress configuration sourceCycle) reversed := by
        unfold InitialReorder.BankLane.writeIndex at indexEqual
        rw [intermediateWrite, targetWriteBank] at indexEqual
        have numeric := congrArg Fin.val indexEqual
        simp only [InitialReorder.BankLane.payloadAddress,
          InitialReorder.BankLane.payloadFields,
          InitialReorder.Lane.resultValue_address,
          BitVector.toIndex_val] at numeric
        exact BitVector.toNat_injective _ numeric
      rw [cycleAddress_addressCycle]
      exact writeAddressEqual.trans targetAddress
    have bankEqual : bankIndex configuration currentCycle selected =
        bankIndex configuration cycle lane := by
      calc
        _ = bank := by
          dsimp only [selected, currentCycle]
          simpa only [cycleAddress_addressCycle] using
            bankIndex_preRotation_source configuration
              (addressCycle configuration address) bank
        _ = _ := rfl
    have coordinateEqual := bankAddress_injective configuration (!reversed)
      bankEqual addressEqual
    have currentBound : currentCycle.val ≤ offset.val := by
      dsimp only [currentCycle, address]
      rw [addressCycle_val]
      exact currentControl.2
    have offsetBefore : offset.val < cycle.val := by
      dsimp only [offset]
      omega
    have cycleEqual := congrArg Fin.val coordinateEqual.1
    omega

/-- One output sample is the globally bit-reversed input sample selected by
the natural frame contract. -/
private theorem output_data_at
    (configuration : Configuration depth)
    {initialState finalState : (reorderStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {hierarchy : List (HierStep (reorderStructure depth configuration))}
    (execution : (reorderStructure depth configuration).ObservedExecutes
      initialState inputs hierarchy finalState)
    (start : Nat)
    (within : start + configuration.initialReorderLatency +
      configuration.frameLength ≤ hierarchy.length)
    (starts : FramedLatency.Starts configuration.frameLength_pos
      (fun input : (InitialReorder.ports configuration).inputs.Values =>
        (show Bool from input .i_first) = true)
      (FramedLatency.window inputs start (by
        rw [← execution.length_eq]
        omega)))
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    (hierarchy.get ⟨start + configuration.initialReorderLatency + cycle.val,
        by omega⟩).outputs .o_data lane =
      (hierarchy.get ⟨start +
        (reversedCycle configuration cycle lane).val, by
          unfold Configuration.initialReorderLatency at within
          omega⟩).inputs .i_data
        (reversedLane configuration cycle lane) := by
  let sourceCycle := reversedCycle configuration cycle lane
  let sourceLane := reversedLane configuration cycle lane
  let bank := bankIndex configuration cycle lane
  let writePosition := start + sourceCycle.val + barrelLatency configuration
  let readPosition := start + configuration.frameLength + cycle.val +
    barrelLatency configuration
  let bankOutputPosition := readPosition + 1
  have controlWithin : start + configuration.frameLength +
      configuration.frameLength ≤ hierarchy.length := by
    unfold Configuration.initialReorderLatency at within
    omega
  obtain ⟨reversed, firstSchedule, continuation⟩ :=
    control_schedule_at configuration execution start (by
      rw [← execution.length_eq]
      exact controlWithin) starts
  have readIn : start + configuration.frameLength + cycle.val +
      barrelLatency configuration < hierarchy.length := by
    unfold Configuration.initialReorderLatency at within
    dsimp only [barrelLatency]
    omega
  have outputIn : bankOutputPosition < hierarchy.length := by
    dsimp only [bankOutputPosition, readPosition]
    unfold Configuration.initialReorderLatency at within
    dsimp only [barrelLatency]
    omega
  have writeIn : writePosition < hierarchy.length := by
    dsimp only [writePosition]
    unfold Configuration.initialReorderLatency at within
    dsimp only [barrelLatency]
    omega
  have readPrepared := bankRead_at configuration execution
    (start + cycle.val) bank (by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using readIn)
  have writePrepared := bankWrite_at configuration execution
    (start + sourceCycle.val) bank writeIn
  have cycleControl := firstSchedule cycle
  have sourceControl := firstSchedule sourceCycle
  have reversedBank : bankIndex configuration sourceCycle sourceLane = bank :=
    bankIndex_reversed configuration cycle lane
  rw [cycleControl.1, cycleControl.2] at readPrepared
  rw [sourceControl.1, sourceControl.2] at writePrepared
  rw [← reversedBank,
    preRotation_sourceIndex configuration sourceCycle sourceLane]
      at writePrepared
  have readAddress :
      ((hierarchy.get ⟨readPosition, by
        dsimp only [readPosition]
        exact readIn⟩).children (.bank bank)).inputs .i_readAddress =
        InitialReorder.Lane.memoryAddress configuration lane
          (cycleAddress configuration cycle) (!reversed) := by
    dsimp only [readPosition, bank] at readPrepared ⊢
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      preRotation_sourceIndex] using readPrepared
  have writePayload :
      ((hierarchy.get ⟨writePosition, writeIn⟩).children
        (.bank bank)).inputs .i_writePayload =
        InitialReorder.Lane.resultValue configuration sourceLane
          ((hierarchy.get ⟨start + sourceCycle.val, by omega⟩).inputs
            .i_data sourceLane)
          (cycleAddress configuration sourceCycle) reversed := by
    dsimp only [writePosition]
    rw [reversedBank] at writePrepared
    exact writePrepared
  let bankExecution := execution.child (.bank bank)
  obtain ⟨bankInitial, bankFinal, bankTrace⟩ :=
    InitialReorder.BankLane.contract_of_execution depth configuration
      bankExecution
  rw [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
    at bankTrace
  change Trace (InitialReorder.BankLane.Transition configuration) bankInitial
    (hierarchy.map fun step => (step.children (.bank bank)).inputs)
    (hierarchy.map fun step => (step.children (.bank bank)).outputs)
    bankFinal at bankTrace
  simp only [List.get_eq_getElem] at readAddress writePayload
  have sameAddress :
      InitialReorder.BankLane.readIndex configuration
          ((hierarchy.map fun step =>
            (step.children (.bank bank)).inputs).get
              ⟨readPosition, by
                simp only [List.length_map]
                dsimp only [readPosition]
                exact readIn⟩) =
        InitialReorder.BankLane.writeIndex configuration
          ((hierarchy.map fun step =>
            (step.children (.bank bank)).inputs).get
              ⟨writePosition, by simp only [List.length_map]; exact writeIn⟩) := by
    simp only [List.get_eq_getElem, List.getElem_map]
    unfold InitialReorder.BankLane.readIndex
      InitialReorder.BankLane.writeIndex
    rw [readAddress, writePayload]
    simp only [InitialReorder.Lane.resultValue_address,
      InitialReorder.BankLane.payloadAddress,
      InitialReorder.BankLane.payloadFields]
    simpa only [sourceCycle, sourceLane, Bool.not_not] using congrArg
      (BitVector.toIndex (InitialReorder.addressWidth configuration))
      (memoryAddress_opposite configuration cycle lane (!reversed)).symm
  have bankOutput := InitialReorder.BankLane.output_after_write configuration
    bankTrace writePosition readPosition (by
      dsimp only [writePosition, readPosition, sourceCycle]
      omega) (by
        simp only [List.length_map]
        simpa only [bankOutputPosition] using outputIn) sameAddress (by
        intro position afterWrite beforeRead
        exact bank_not_overwritten configuration execution start reversed
          controlWithin firstSchedule continuation cycle lane readIn position
          (by simpa only [writePosition] using afterWrite)
          (by simpa only [readPosition] using beforeRead))
  have bankValue :
      ((hierarchy.get ⟨bankOutputPosition, outputIn⟩).children
        (.bank bank)).outputs .o_data =
        ((hierarchy.get ⟨start + sourceCycle.val, by omega⟩).inputs
          .i_data sourceLane) := by
    simp only [List.get_eq_getElem, List.getElem_map] at bankOutput
    unfold InitialReorder.BankLane.writeData at bankOutput
    rw [writePayload] at bankOutput
    simp only [InitialReorder.BankLane.payloadData,
      InitialReorder.BankLane.payloadFields,
      InitialReorder.Lane.resultValue_data] at bankOutput
    simpa only [bankOutputPosition, List.get_eq_getElem] using bankOutput
  have rotation := postRotation_at configuration execution
    (start + cycle.val) (by
      unfold Configuration.initialReorderLatency at within
      omega)
  rw [cycleControl.1] at rotation
  have rotationAt :
      ((hierarchy.get ⟨bankOutputPosition, outputIn⟩).children
        .postRotationAlign).outputs .output =
        InitialReorder.laneRotation configuration
          (cycleAddress configuration cycle) := by
    simpa only [bankOutputPosition, readPosition, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using rotation
  have finalData := postBarrel_at configuration execution
    bankOutputPosition (by
      dsimp only [bankOutputPosition, readPosition]
      unfold Configuration.initialReorderLatency at within
      dsimp only [barrelLatency] at within ⊢
      omega)
  have finalPosition : bankOutputPosition + barrelLatency configuration =
      start + configuration.initialReorderLatency + cycle.val := by
    dsimp only [bankOutputPosition, readPosition]
    unfold Configuration.initialReorderLatency
    dsimp only [barrelLatency]
    omega
  rw [rotationAt] at finalData
  have selected := congrFun finalData lane
  rw [postRotation_result_at_lane] at selected
  change _ = _ at selected
  rw [bankValue] at selected
  simpa only [finalPosition, bank] using selected

/-- The concrete hierarchy satisfies the natural framed bit-reversal
contract. -/
theorem contract_of_execution
    (depth : Nat) (configuration : Configuration depth)
    {initialState finalState :
      (InitialReorder.moduleStructure depth configuration).State}
    {inputs : List (InitialReorder.ports configuration).inputs.Values}
    {outputs : List (InitialReorder.ports configuration).outputs.Values}
    (execution : (InitialReorder.moduleStructure depth configuration).Executes
      initialState inputs outputs finalState) :
    InitialReorder.contract configuration execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, hierarchyOutputs⟩ := execution.observe
  unfold InitialReorder.contract FramedLatency.Holds FramedLatency.Relates
  rw [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  constructor
  · exact execution.length_eq
  · intro start inputWithin outputWithin starts
    have hierarchyLength : hierarchy.length = outputs.length := by
      have equal := congrArg List.length hierarchyOutputs
      simpa only [List.length_map] using equal
    have hierarchyWithin : start + configuration.initialReorderLatency +
        configuration.frameLength ≤ hierarchy.length := by
      rw [hierarchyLength]
      exact outputWithin
    constructor
    · exact output_starts configuration observed hierarchyOutputs start
        inputWithin outputWithin starts
    · unfold InitialReorder.frameRelation InitialReorder.carriedRelation
      funext cycle lane
      rw [resultFrame_at]
      have outputInHierarchy :
          start + configuration.initialReorderLatency + cycle.val <
            hierarchy.length := by omega
      have outputInOutputs :
          start + configuration.initialReorderLatency + cycle.val <
            outputs.length := by omega
      have sourceInHierarchy :
          start + (reversedCycle configuration cycle lane).val <
            hierarchy.length := by
        rw [observed.length_eq]
        omega
      have sourceInInputs :
          start + (reversedCycle configuration cycle lane).val <
            inputs.length := by omega
      have outputBoundary := observed.output_at hierarchyOutputs
        (start + configuration.initialReorderLatency + cycle.val)
        outputInHierarchy outputInOutputs
      have inputBoundary := observed.input_at
        (start + (reversedCycle configuration cycle lane).val)
        sourceInHierarchy sourceInInputs
      simp only [FramedLatency.window_apply]
      rw [← outputBoundary, ← inputBoundary]
      exact output_data_at configuration observed start hierarchyWithin starts
        cycle lane

end HTFFT.Silean.InitialReorder.Internal
