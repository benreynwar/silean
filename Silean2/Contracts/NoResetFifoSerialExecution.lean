import Silean2.Contracts.NoResetFifoView

namespace Silean2.Contracts.NoResetFifo.Execution

structure StepDecomposition
    {OuterState UpstreamState DownstreamState Word : Type}
    (outer : Model OuterState Word)
    (upstream : Model UpstreamState Word)
    (downstream : Model DownstreamState Word)
    (upstreamState : OuterState → UpstreamState)
    (downstreamState : OuterState → DownstreamState)
    (childInputs : OuterState → Input Word → Input Word × Input Word)
    (state : OuterState) (input : Input Word) : Prop where
  upstreamNext :
    upstreamState (outer.step state input).nextState =
      (upstream.step (upstreamState state) (childInputs state input).1).nextState
  downstreamNext :
    downstreamState (outer.step state input).nextState =
      (downstream.step (downstreamState state) (childInputs state input).2).nextState
  connected : NoResetFifo.SerialCycle
    (outer.step state input).cycle
    (upstream.step (upstreamState state) (childInputs state input).1).cycle
    (downstream.step (downstreamState state) (childInputs state input).2).cycle

structure Serial
    {OuterState UpstreamState DownstreamState Word : Type}
    (outer : Model OuterState Word)
    (upstream : Model UpstreamState Word)
    (downstream : Model DownstreamState Word) where
  upstreamState : OuterState → UpstreamState
  downstreamState : OuterState → DownstreamState
  childInputs : OuterState → Input Word → Input Word × Input Word
  step_decomposes : ∀ state input,
    StepDecomposition outer upstream downstream upstreamState downstreamState
      childInputs state input

namespace Serial

def childInputLists
    {OuterState UpstreamState DownstreamState Word : Type}
    {outer : Model OuterState Word} {upstream : Model UpstreamState Word}
    {downstream : Model DownstreamState Word}
    (serial : Serial outer upstream downstream) :
    OuterState → List (Input Word) →
      List (Input Word) × List (Input Word)
  | _, [] => ([], [])
  | state, input :: inputs =>
      let childInput := serial.childInputs state input
      let rest := serial.childInputLists
        (outer.step state input).nextState inputs
      (childInput.1 :: rest.1, childInput.2 :: rest.2)

structure RunDecomposition
    {OuterState UpstreamState DownstreamState Word : Type}
    {outer : Model OuterState Word} {upstream : Model UpstreamState Word}
    {downstream : Model DownstreamState Word}
    (serial : Serial outer upstream downstream)
    (initial : OuterState) (inputs : List (Input Word)) : Prop where
  upstreamFinal :
    serial.upstreamState (outer.run initial inputs).finalState =
      (upstream.run (serial.upstreamState initial)
        (serial.childInputLists initial inputs).1).finalState
  downstreamFinal :
    serial.downstreamState (outer.run initial inputs).finalState =
      (downstream.run (serial.downstreamState initial)
        (serial.childInputLists initial inputs).2).finalState
  connected : NoResetFifo.SerialCycles
    (outer.run initial inputs).cycles
    (upstream.run (serial.upstreamState initial)
      (serial.childInputLists initial inputs).1).cycles
    (downstream.run (serial.downstreamState initial)
      (serial.childInputLists initial inputs).2).cycles

theorem run_decomposes
    {OuterState UpstreamState DownstreamState Word : Type}
    {outer : Model OuterState Word} {upstream : Model UpstreamState Word}
    {downstream : Model DownstreamState Word}
    (serial : Serial outer upstream downstream)
    (initial : OuterState) (inputs : List (Input Word)) :
    serial.RunDecomposition initial inputs := by
  induction inputs generalizing initial with
  | nil => exact ⟨rfl, rfl, .nil⟩
  | cons input inputs induction =>
      have head := serial.step_decomposes initial input
      have tail := induction (outer.step initial input).nextState
      refine ⟨?_, ?_, ?_⟩
      · simp only [Model.run, childInputLists]
        rw [← head.upstreamNext]
        exact tail.upstreamFinal
      · simp only [Model.run, childInputLists]
        rw [← head.downstreamNext]
        exact tail.downstreamFinal
      · simp only [Model.run, childInputLists]
        rw [← head.upstreamNext, ← head.downstreamNext]
        exact NoResetFifo.SerialCycles.cons head.connected tail.connected

end Serial

end Silean2.Contracts.NoResetFifo.Execution

namespace Silean2.Contracts.NoResetFifo.View.Execution

open NoResetFifo.Execution

structure Constructor
    (outerView : View OuterState Word)
    (upstreamView : View UpstreamState Word)
    (downstreamView : View DownstreamState Word)
    (outer : Model OuterState Word)
    (upstream : Model UpstreamState Word)
    (downstream : Model DownstreamState Word) where
  serial : NoResetFifo.Execution.Serial outer upstream downstream
  contents : ∀ state,
    outerView.contents state =
      downstreamView.contents (serial.downstreamState state) ++
        upstreamView.contents (serial.upstreamState state)

namespace Constructor

def outerExecutes (_constructor : Constructor outerView upstreamView
    downstreamView outer upstream downstream) :
    View.ExecutionRelation outerView := outer.executes

def upstreamExecutes (_constructor : Constructor outerView upstreamView
    downstreamView outer upstream downstream) :
    View.ExecutionRelation upstreamView := upstream.executes

def downstreamExecutes (_constructor : Constructor outerView upstreamView
    downstreamView outer upstream downstream) :
    View.ExecutionRelation downstreamView := downstream.executes

theorem execution_decomposes
    {outerView : View OuterState Word}
    {upstreamView : View UpstreamState Word}
    {downstreamView : View DownstreamState Word}
    {outer : Model OuterState Word}
    {upstream : Model UpstreamState Word}
    {downstream : Model DownstreamState Word}
    (constructor : Constructor outerView upstreamView downstreamView
      outer upstream downstream)
    (initial : OuterState)
    (cycles : List (NoResetFifo.Cycle Word))
    (final : OuterState)
    (execution : constructor.outerExecutes initial cycles final) :
    View.SerialExecutionDecomposition outerView upstreamView downstreamView
      constructor.upstreamExecutes constructor.downstreamExecutes
      initial cycles final := by
  rcases execution with ⟨inputs, cyclesEqual, finalEqual⟩
  let childInputs := constructor.serial.childInputLists initial inputs
  let split := constructor.serial.run_decomposes initial inputs
  let upstreamInitial := constructor.serial.upstreamState initial
  let downstreamInitial := constructor.serial.downstreamState initial
  let upstreamFinal := constructor.serial.upstreamState final
  let downstreamFinal := constructor.serial.downstreamState final
  let upstreamRun := upstream.run upstreamInitial childInputs.1
  let downstreamRun := downstream.run downstreamInitial childInputs.2
  have upstreamFinalEqual : upstreamRun.finalState = upstreamFinal := by
    dsimp [upstreamRun, upstreamInitial, upstreamFinal]
    rw [← split.upstreamFinal, finalEqual]
  have downstreamFinalEqual : downstreamRun.finalState = downstreamFinal := by
    dsimp [downstreamRun, downstreamInitial, downstreamFinal]
    rw [← split.downstreamFinal, finalEqual]
  refine ⟨upstreamInitial, upstreamRun.cycles, upstreamFinal,
    downstreamInitial, downstreamRun.cycles, downstreamFinal,
    ⟨childInputs.1, rfl, upstreamFinalEqual⟩,
    ⟨childInputs.2, rfl, downstreamFinalEqual⟩, ?_,
    constructor.contents initial, constructor.contents final⟩
  rw [← cyclesEqual]
  exact split.connected

theorem satisfies
    {outerView : View OuterState Word}
    {upstreamView : View UpstreamState Word}
    {downstreamView : View DownstreamState Word}
    {outer : Model OuterState Word}
    {upstream : Model UpstreamState Word}
    {downstream : Model DownstreamState Word}
    (constructor : Constructor outerView upstreamView downstreamView
      outer upstream downstream)
    (capacity : outerView.capacity =
      upstreamView.capacity + downstreamView.capacity)
    (readyPropagationLatency : outerView.readyPropagationLatency =
      upstreamView.readyPropagationLatency +
        downstreamView.readyPropagationLatency)
    (upstreamSatisfies : View.Satisfies upstreamView
      constructor.upstreamExecutes)
    (downstreamSatisfies : View.Satisfies downstreamView
      constructor.downstreamExecutes) :
    View.Satisfies outerView constructor.outerExecutes :=
  View.Satisfies.serial capacity readyPropagationLatency
    upstreamSatisfies downstreamSatisfies constructor.execution_decomposes

end Constructor

end Silean2.Contracts.NoResetFifo.View.Execution
