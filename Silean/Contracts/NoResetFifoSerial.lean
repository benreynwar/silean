import Silean.Contracts.NoResetFifo

namespace Silean.Contracts.NoResetFifo

structure SerialCycle (outer upstream downstream : Cycle Word) : Prop where
  externalEnqValid : outer.enqValid = upstream.enqValid
  externalEnqData : outer.enqData = upstream.enqData
  externalEnqReady : outer.enqReady = upstream.enqReady
  internalValid : upstream.deqValid = downstream.enqValid
  internalData : upstream.deqData = downstream.enqData
  internalReady : upstream.deqReady = downstream.enqReady
  externalDeqValid : downstream.deqValid = outer.deqValid
  externalDeqData : downstream.deqData = outer.deqData
  externalDeqReady : downstream.deqReady = outer.deqReady

inductive SerialCycles : List (Cycle Word) → List (Cycle Word) →
    List (Cycle Word) → Prop
  | nil : SerialCycles [] [] []
  | cons : SerialCycle outer upstream downstream →
      SerialCycles outers upstreams downstreams →
      SerialCycles (outer :: outers) (upstream :: upstreams)
        (downstream :: downstreams)

namespace SerialCycles

theorem externalInputs
    (connected : SerialCycles outer upstream downstream) :
    acceptedInputs outer = acceptedInputs upstream := by
  induction connected with
  | nil => rfl
  | cons head _ induction =>
    simp only [acceptedInputs]
    rw [induction]
    congr 1
    cases head
    simp_all [Cycle.acceptedInput]

theorem externalOutputs
    (connected : SerialCycles outer upstream downstream) :
    acceptedOutputs outer = acceptedOutputs downstream := by
  induction connected with
  | nil => rfl
  | cons head _ induction =>
    simp only [acceptedOutputs]
    rw [induction]
    congr 1
    cases head
    simp_all [Cycle.acceptedOutput]

theorem internalTransfers
    (connected : SerialCycles outer upstream downstream) :
    acceptedOutputs upstream = acceptedInputs downstream := by
  induction connected with
  | nil => rfl
  | cons head _ induction =>
    simp only [acceptedOutputs, acceptedInputs]
    rw [induction]
    congr 1
    cases head
    simp_all [Cycle.acceptedInput, Cycle.acceptedOutput]

theorem inputStalls
    (connected : SerialCycles outer upstream downstream) :
    inputReadyStalls outer = inputReadyStalls upstream := by
  induction connected with
  | nil => rfl
  | cons head _ induction =>
    simp only [inputReadyStalls]
    rw [induction]
    cases head
    simp_all

theorem internalStalls
    (connected : SerialCycles outer upstream downstream) :
    outputReadyStalls upstream = inputReadyStalls downstream := by
  induction connected with
  | nil => rfl
  | cons head _ induction =>
    simp only [outputReadyStalls, inputReadyStalls]
    rw [induction]
    cases head
    simp_all

theorem outputStalls
    (connected : SerialCycles outer upstream downstream) :
    outputReadyStalls downstream = outputReadyStalls outer := by
  induction connected with
  | nil => rfl
  | cons head _ induction =>
    simp only [outputReadyStalls]
    rw [induction]
    cases head
    simp_all

end SerialCycles

structure SerialDecomposition (upstreamCapacity downstreamCapacity : Nat)
    (outer upstream downstream : Trace Word) : Prop where
  initialContents :
    outer.initialContents =
      downstream.initialContents ++ upstream.initialContents
  finalContents :
    outer.finalContents = downstream.finalContents ++ upstream.finalContents
  externalInputs :
    acceptedInputs outer.cycles = acceptedInputs upstream.cycles
  externalOutputs :
    acceptedOutputs outer.cycles = acceptedOutputs downstream.cycles
  internalTransfers :
    acceptedOutputs upstream.cycles = acceptedInputs downstream.cycles
  inputStalls :
    inputReadyStalls outer.cycles = inputReadyStalls upstream.cycles
  internalStalls :
    outputReadyStalls upstream.cycles = inputReadyStalls downstream.cycles
  outputStalls :
    outputReadyStalls downstream.cycles = outputReadyStalls outer.cycles
  upstreamInitialCapacity :
    upstream.initialContents.length ≤ upstreamCapacity
  downstreamInitialCapacity :
    downstream.initialContents.length ≤ downstreamCapacity

namespace SerialDecomposition

theorem ofCycles
    (connected : SerialCycles outer.cycles upstream.cycles downstream.cycles)
    (initialContents : outer.initialContents =
      downstream.initialContents ++ upstream.initialContents)
    (finalContents : outer.finalContents =
      downstream.finalContents ++ upstream.finalContents)
    (upstreamInitialCapacity :
      upstream.initialContents.length ≤ upstreamCapacity)
    (downstreamInitialCapacity :
      downstream.initialContents.length ≤ downstreamCapacity) :
    SerialDecomposition upstreamCapacity downstreamCapacity
      outer upstream downstream where
  initialContents := initialContents
  finalContents := finalContents
  externalInputs := connected.externalInputs
  externalOutputs := connected.externalOutputs
  internalTransfers := connected.internalTransfers
  inputStalls := connected.inputStalls
  internalStalls := connected.internalStalls
  outputStalls := connected.outputStalls
  upstreamInitialCapacity := upstreamInitialCapacity
  downstreamInitialCapacity := downstreamInitialCapacity

end SerialDecomposition

namespace Contract

theorem serial_readyPropagation
    {outer upstream downstream : Trace Word}
    {upstreamCapacity downstreamCapacity upstreamLatency downstreamLatency : Nat}
    (decomposition : SerialDecomposition upstreamCapacity downstreamCapacity
      outer upstream downstream)
    (upstreamContract : Contract upstreamCapacity upstreamLatency upstream)
    (downstreamContract : Contract downstreamCapacity downstreamLatency downstream) :
    inputReadyStalls outer.cycles ≤
      outputReadyStalls outer.cycles + (upstreamLatency + downstreamLatency) := by
  rw [decomposition.inputStalls]
  calc
    inputReadyStalls upstream.cycles ≤
        outputReadyStalls upstream.cycles + upstreamLatency :=
      upstreamContract.readyPropagation
    _ = inputReadyStalls downstream.cycles + upstreamLatency := by
      rw [decomposition.internalStalls]
    _ ≤ (outputReadyStalls downstream.cycles + downstreamLatency) +
          upstreamLatency :=
      Nat.add_le_add_right downstreamContract.readyPropagation _
    _ = outputReadyStalls outer.cycles +
          (upstreamLatency + downstreamLatency) := by
      rw [decomposition.outputStalls]
      omega

theorem serial
    {outer upstream downstream : Trace Word}
    {upstreamCapacity downstreamCapacity upstreamLatency downstreamLatency : Nat}
    (decomposition : SerialDecomposition upstreamCapacity downstreamCapacity
      outer upstream downstream)
    (upstreamContract : Contract upstreamCapacity upstreamLatency upstream)
    (downstreamContract : Contract downstreamCapacity downstreamLatency downstream) :
    Contract (upstreamCapacity + downstreamCapacity)
      (upstreamLatency + downstreamLatency) outer where
  conservation := by
    rw [decomposition.initialContents, decomposition.externalInputs,
      decomposition.externalOutputs, decomposition.finalContents]
    calc
      (downstream.initialContents ++ upstream.initialContents) ++
          acceptedInputs upstream.cycles =
        downstream.initialContents ++
          (upstream.initialContents ++ acceptedInputs upstream.cycles) := by
            simp [List.append_assoc]
      _ = downstream.initialContents ++
          (acceptedOutputs upstream.cycles ++ upstream.finalContents) := by
            rw [upstreamContract.conservation]
      _ = (downstream.initialContents ++ acceptedInputs downstream.cycles) ++
          upstream.finalContents := by
            rw [decomposition.internalTransfers]
            simp [List.append_assoc]
      _ = (acceptedOutputs downstream.cycles ++ downstream.finalContents) ++
          upstream.finalContents := by
            rw [downstreamContract.conservation]
      _ = acceptedOutputs downstream.cycles ++
          (downstream.finalContents ++ upstream.finalContents) := by
            simp [List.append_assoc]
  capacity _ := by
    have upstreamFinalBound :=
      upstreamContract.capacity decomposition.upstreamInitialCapacity
    have downstreamFinalBound :=
      downstreamContract.capacity decomposition.downstreamInitialCapacity
    rw [decomposition.finalContents, List.length_append]
    omega
  readyPropagation := serial_readyPropagation decomposition
    upstreamContract downstreamContract

end Contract

end Silean.Contracts.NoResetFifo
