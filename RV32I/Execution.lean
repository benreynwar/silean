import RV32I.Decoder

namespace RV32I

/-- The finite architectural record kept by a multi-instruction execution.
External effects and instruction results are separate, ordered sequences. -/
structure ExecutionTrace where
  effects : List Effect
  results : List InstructionResult

namespace ExecutionTrace

def empty : ExecutionTrace :=
  { effects := []
    results := [] }

/-- Concatenate two consecutive execution records. -/
def append (first second : ExecutionTrace) : ExecutionTrace :=
  { effects := first.effects ++ second.effects
    results := first.results ++ second.results }

/-- Add one completed instruction and its effects before a later trace. -/
def prepend (effects : List Effect) (result : InstructionResult)
    (later : ExecutionTrace) : ExecutionTrace :=
  { effects := effects ++ later.effects
    results := result :: later.results }

@[simp] theorem effects_empty : empty.effects = [] := rfl

@[simp] theorem results_empty : empty.results = [] := rfl

@[simp] theorem effects_append (first second : ExecutionTrace) :
    (first.append second).effects = first.effects ++ second.effects := rfl

@[simp] theorem results_append (first second : ExecutionTrace) :
    (first.append second).results = first.results ++ second.results := rfl

@[simp] theorem effects_prepend (effects : List Effect)
    (result : InstructionResult) (later : ExecutionTrace) :
    (prepend effects result later).effects = effects ++ later.effects := rfl

@[simp] theorem results_prepend (effects : List Effect)
    (result : InstructionResult) (later : ExecutionTrace) :
    (prepend effects result later).results = result :: later.results := rfl

@[simp] theorem empty_append (trace : ExecutionTrace) :
    empty.append trace = trace := by
  cases trace
  rfl

@[simp] theorem append_empty (trace : ExecutionTrace) :
    trace.append empty = trace := by
  cases trace
  simp [append, empty]

theorem append_assoc (first second third : ExecutionTrace) :
    (first.append second).append third = first.append (second.append third) := by
  cases first
  cases second
  cases third
  simp [append, List.append_assoc]

theorem prepend_append (effects : List Effect) (result : InstructionResult)
    (first second : ExecutionTrace) :
    (prepend effects result first).append second =
      prepend effects result (first.append second) := by
  cases first
  cases second
  simp [prepend, append, List.append_assoc]

end ExecutionTrace

/-- Why a finite unprivileged execution segment stopped.

`prefix` is a voluntary finite-prefix boundary after zero or more retired
instructions. `raised` ends this unprivileged segment at an exception; it does
not assert machine termination or perform EEI trap handling. -/
inductive ExecutionBoundary where
  | prefix
  | raised (exception : Exception)
  deriving DecidableEq, Repr

namespace Execution

/-- Finite execution against an abstract relational EEI.

Each instruction is the existing fetch/decode/execute interaction. Retirement
passes its exact successor hart state and resulting EEI state to the rest of
the execution. A raised exception records the faulting state and closes only
the current unprivileged segment. -/
inductive Runs {environmentState : Type}
    (environment : ExecutionEnvironment environmentState) :
    State → environmentState → ExecutionTrace → ExecutionBoundary →
      State → environmentState → Prop where
  | stop (hart : State) (eei : environmentState) :
      Runs environment hart eei .empty .prefix hart eei
  | retired
      (hart nextHart finalHart : State)
      (before middle after : environmentState)
      (aligned : hart.pc.toNat % 4 = 0)
      (instructionEffects : List Effect)
      (laterTrace : ExecutionTrace)
      (boundary : ExecutionBoundary)
      (instructionRuns :
        Interaction.Runs environment
          (Decoder.fetchDecodeExecute hart aligned) before instructionEffects
          (.retired nextHart) middle)
      (laterRuns :
        Runs environment nextHart middle laterTrace boundary finalHart after) :
      Runs environment hart before
        (.prepend instructionEffects (.retired nextHart) laterTrace)
        boundary finalHart after
  | raised
      (hart faultingHart : State)
      (before after : environmentState)
      (aligned : hart.pc.toNat % 4 = 0)
      (instructionEffects : List Effect)
      (exception : Exception)
      (instructionRuns :
        Interaction.Runs environment
          (Decoder.fetchDecodeExecute hart aligned) before instructionEffects
          (.raised faultingHart exception) after) :
      Runs environment hart before
        { effects := instructionEffects
          results := [.raised faultingHart exception] }
        (.raised exception) faultingHart after

/-- A zero-instruction execution is a prefix with unchanged hart and EEI
states and an empty trace. -/
theorem zero (environment : ExecutionEnvironment environmentState)
    (hart : State) (eei : environmentState) :
    Runs environment hart eei .empty .prefix hart eei := by
  exact .stop hart eei

/-- Extend an existing execution at its front with one retired instruction.
The constructor's shared `nextHart` and `middle` arguments state both hart and
EEI continuity explicitly. -/
theorem extendRetired
    {environment : ExecutionEnvironment environmentState}
    {hart nextHart finalHart : State}
    {before middle after : environmentState}
    {aligned : hart.pc.toNat % 4 = 0}
    {instructionEffects : List Effect}
    {laterTrace : ExecutionTrace}
    {boundary : ExecutionBoundary}
    (instructionRuns :
      Interaction.Runs environment
        (Decoder.fetchDecodeExecute hart aligned) before instructionEffects
        (.retired nextHart) middle)
    (laterRuns :
      Runs environment nextHart middle laterTrace boundary finalHart after) :
    Runs environment hart before
      (.prepend instructionEffects (.retired nextHart) laterTrace)
      boundary finalHart after := by
  exact .retired hart nextHart finalHart before middle after aligned
    instructionEffects laterTrace boundary instructionRuns laterRuns

/-- Compose two retired instructions into a two-instruction finite prefix.
The intermediate hart and EEI states are shared in the two premises, and the
first instruction's effects precede the second instruction's effects. -/
theorem twoRetired
    {environment : ExecutionEnvironment environmentState}
    {firstHart secondHart thirdHart : State}
    {firstEEI secondEEI thirdEEI : environmentState}
    {firstAligned : firstHart.pc.toNat % 4 = 0}
    {secondAligned : secondHart.pc.toNat % 4 = 0}
    {firstEffects secondEffects : List Effect}
    (firstRuns :
      Interaction.Runs environment
        (Decoder.fetchDecodeExecute firstHart firstAligned)
        firstEEI firstEffects (.retired secondHart) secondEEI)
    (secondRuns :
      Interaction.Runs environment
        (Decoder.fetchDecodeExecute secondHart secondAligned)
        secondEEI secondEffects (.retired thirdHart) thirdEEI) :
    Runs environment firstHart firstEEI
      { effects := firstEffects ++ secondEffects
        results := [.retired secondHart, .retired thirdHart] }
      .prefix thirdHart thirdEEI := by
  have stopped :
      Runs environment thirdHart thirdEEI .empty .prefix thirdHart thirdEEI :=
    .stop thirdHart thirdEEI
  have secondPrefix :=
    extendRetired secondRuns stopped
  have both :=
    extendRetired firstRuns secondPrefix
  simpa [ExecutionTrace.prepend, ExecutionTrace.empty] using both

/-- Concatenate a finite prefix with a following execution. This theorem is
intentionally restricted to `.prefix`; a raised segment cannot be continued
without a separate EEI trap-disposition relation. -/
theorem append_prefix
    {environment : ExecutionEnvironment environmentState}
    {initial middle final : State}
    {initialEEI middleEEI finalEEI : environmentState}
    {first second : ExecutionTrace}
    {boundary : ExecutionBoundary}
    (firstRuns :
      Runs environment initial initialEEI first .prefix middle middleEEI)
    (secondRuns :
      Runs environment middle middleEEI second boundary final finalEEI) :
    Runs environment initial initialEEI (first.append second)
      boundary final finalEEI := by
  generalize boundaryEq : (ExecutionBoundary.prefix) = firstBoundary at firstRuns
  induction firstRuns with
  | stop => simpa using secondRuns
  | retired hart nextHart _ before nextEEI _ aligned effects later _ step rest ih =>
      rw [ExecutionTrace.prepend_append]
      exact .retired hart nextHart final before nextEEI finalEEI aligned effects
        (later.append second) boundary step (ih secondRuns boundaryEq)
  | raised => cases boundaryEq

end Execution

end RV32I
