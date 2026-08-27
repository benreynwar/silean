import Silean2.Contracts.NoResetFifoExecution
import Silean2.Contracts.NoResetFifoSerial

namespace Silean2.Contracts.NoResetFifo

structure View (State Word : Type) where
  contents : State → List Word
  capacity : Nat
  readyPropagationLatency : Nat
  contents_bounded : ∀ state, (contents state).length ≤ capacity

namespace View

def trace (view : View State Word)
    (initial : State) (cycles : List (Cycle Word))
    (final : State) : Trace Word where
  initialContents := view.contents initial
  cycles := cycles
  finalContents := view.contents final

abbrev ExecutionRelation (_view : View State Word) : Type :=
  State → List (Cycle Word) → State → Prop

def Satisfies (view : View State Word)
    (executes : ExecutionRelation view) : Prop :=
  ∀ initial cycles final, executes initial cycles final →
    Contract view.capacity view.readyPropagationLatency
      (view.trace initial cycles final)

def SerialExecutionDecomposition
    (outerView : View OuterState Word)
    (upstreamView : View UpstreamState Word)
    (downstreamView : View DownstreamState Word)
    (upstreamExecutes : ExecutionRelation upstreamView)
    (downstreamExecutes : ExecutionRelation downstreamView)
    (outerInitial : OuterState)
    (outerCycles : List (Cycle Word))
    (outerFinal : OuterState) : Prop :=
  ∃ upstreamInitial upstreamCycles upstreamFinal
      downstreamInitial downstreamCycles downstreamFinal,
    upstreamExecutes upstreamInitial upstreamCycles upstreamFinal ∧
    downstreamExecutes downstreamInitial downstreamCycles downstreamFinal ∧
    SerialCycles outerCycles upstreamCycles downstreamCycles ∧
    outerView.contents outerInitial =
      downstreamView.contents downstreamInitial ++
        upstreamView.contents upstreamInitial ∧
    outerView.contents outerFinal =
      downstreamView.contents downstreamFinal ++
        upstreamView.contents upstreamFinal

theorem Satisfies.serial
    {outerView : View OuterState Word}
    {upstreamView : View UpstreamState Word}
    {downstreamView : View DownstreamState Word}
    {outerExecutes : ExecutionRelation outerView}
    {upstreamExecutes : ExecutionRelation upstreamView}
    {downstreamExecutes : ExecutionRelation downstreamView}
    (capacity : outerView.capacity =
      upstreamView.capacity + downstreamView.capacity)
    (readyPropagationLatency : outerView.readyPropagationLatency =
      upstreamView.readyPropagationLatency +
        downstreamView.readyPropagationLatency)
    (upstreamSatisfies : Satisfies upstreamView upstreamExecutes)
    (downstreamSatisfies : Satisfies downstreamView downstreamExecutes)
    (decompose : ∀ initial cycles final,
      outerExecutes initial cycles final →
      SerialExecutionDecomposition outerView upstreamView downstreamView
        upstreamExecutes downstreamExecutes initial cycles final) :
    Satisfies outerView outerExecutes := by
  intro initial cycles final outerExecution
  rcases decompose initial cycles final outerExecution with
    ⟨upstreamInitial, upstreamCycles, upstreamFinal,
      downstreamInitial, downstreamCycles, downstreamFinal,
      upstreamExecution, downstreamExecution, connected,
      initialContents, finalContents⟩
  have upstreamContractProof := upstreamSatisfies
    upstreamInitial upstreamCycles upstreamFinal upstreamExecution
  have downstreamContractProof := downstreamSatisfies
    downstreamInitial downstreamCycles downstreamFinal downstreamExecution
  rw [capacity, readyPropagationLatency]
  apply Contract.serial
    (SerialDecomposition.ofCycles connected initialContents finalContents
      (upstreamView.contents_bounded upstreamInitial)
      (downstreamView.contents_bounded downstreamInitial))
    upstreamContractProof downstreamContractProof

end View

namespace Execution.Model

def executes (model : Execution.Model State Word) :
    State → List (Cycle Word) → State → Prop :=
  fun initial cycles final =>
    ∃ inputs, (model.run initial inputs).observations = cycles ∧
      (model.run initial inputs).finalState = final

end Execution.Model

end Silean2.Contracts.NoResetFifo
