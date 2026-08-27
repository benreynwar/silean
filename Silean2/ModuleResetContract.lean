import Silean2.Foundation.Execution
import Silean2.Foundation.ModulePorts
import Silean2.Foundation.SignalExpectation

namespace Silean2

universe u

/-! An exact-cycle behavioral contract synchronized by a bit-valued,
synchronous reset input. Its state is unconstrained Lean data and need not
resemble structural state. -/

structure ModuleResetContract (ports : ModulePorts) where
  State : Type u
  resetInput : ports.inputs.Label
  resetInputType : ports.inputs.signalType resetInput = .bit
  resetState : State
  step : ports.inputs.Values → State → ports.outputs.Expectations × State

namespace ModuleResetContract

def resetAsserted (contract : ModuleResetContract ports)
    (inputs : ports.inputs.Values) : Bool :=
  cast (congrArg SignalType.Denote contract.resetInputType)
    (inputs contract.resetInput)

abbrev Synchronization (contract : ModuleResetContract ports) := Option contract.State

inductive CycleMatches (contract : ModuleResetContract ports) :
    ports.inputs.Values → contract.Synchronization → ports.outputs.Values →
      contract.Synchronization → Prop
  | reset {synchronization input output}
      (asserted : contract.resetAsserted input = true) :
      CycleMatches contract input synchronization output (some contract.resetState)
  | beforeReset {input output}
      (ordinary : contract.resetAsserted input = false) :
      CycleMatches contract input none output none
  | ordinary {state input output}
      (notReset : contract.resetAsserted input = false)
      (outputMatches : ports.outputs.Matches (contract.step input state).1 output) :
      CycleMatches contract input (some state) output
        (some (contract.step input state).2)

abbrev TraceMatches (contract : ModuleResetContract ports) :=
  Execution.Trace contract.CycleMatches

def Accepts (contract : ModuleResetContract ports)
    (inputs : List ports.inputs.Values) (outputs : List ports.outputs.Values) : Prop :=
  ∃ finalSynchronization,
    contract.TraceMatches none inputs outputs finalSynchronization

@[simp] theorem CycleMatches.reset_iff
    (contract : ModuleResetContract ports) {synchronization : contract.Synchronization}
    {input : ports.inputs.Values} {output : ports.outputs.Values}
    {nextSynchronization : contract.Synchronization}
    (asserted : contract.resetAsserted input = true) :
    contract.CycleMatches input synchronization output nextSynchronization ↔
      nextSynchronization = some contract.resetState := by
  constructor
  · intro cycle
    cases cycle with
    | reset => rfl
    | beforeReset ordinary => simp [asserted] at ordinary
    | ordinary notReset _ => simp [asserted] at notReset
  · intro equal
    cases equal
    exact .reset asserted

@[simp] theorem CycleMatches.beforeReset_iff
    (contract : ModuleResetContract ports) {input : ports.inputs.Values}
    {output : ports.outputs.Values} {nextSynchronization : contract.Synchronization}
    (notReset : contract.resetAsserted input = false) :
    contract.CycleMatches input none output nextSynchronization ↔
      nextSynchronization = none := by
  constructor
  · intro cycle
    cases cycle with
    | reset asserted => simp [notReset] at asserted
    | beforeReset => rfl
  · intro equal
    cases equal
    exact .beforeReset notReset

@[simp] theorem CycleMatches.ordinary_iff
    (contract : ModuleResetContract ports) {state : contract.State}
    {input : ports.inputs.Values} {output : ports.outputs.Values}
    {nextSynchronization : contract.Synchronization}
    (notReset : contract.resetAsserted input = false) :
    contract.CycleMatches input (some state) output nextSynchronization ↔
      ports.outputs.Matches (contract.step input state).1 output ∧
        nextSynchronization = some (contract.step input state).2 := by
  constructor
  · intro cycle
    cases cycle with
    | reset asserted => simp [notReset] at asserted
    | ordinary _ outputMatches => exact ⟨outputMatches, rfl⟩
  · rintro ⟨outputMatches, equal⟩
    cases equal
    exact .ordinary notReset outputMatches

theorem TraceMatches.length_eq
    {contract : ModuleResetContract ports}
    {initial final : contract.Synchronization} {inputs : List ports.inputs.Values}
    {outputs : List ports.outputs.Values}
    (trace : contract.TraceMatches initial inputs outputs final) :
    outputs.length = inputs.length :=
  Execution.Trace.length_eq trace

@[simp] theorem TraceMatches.nil_iff
    {contract : ModuleResetContract ports} {initial final : contract.Synchronization} :
    contract.TraceMatches initial [] [] final ↔ final = initial :=
  Execution.Trace.nil_iff

theorem TraceMatches.cons_iff
    {contract : ModuleResetContract ports}
    {initial final : contract.Synchronization} {input : ports.inputs.Values}
    {inputs : List ports.inputs.Values} {output : ports.outputs.Values}
    {outputs : List ports.outputs.Values} :
    contract.TraceMatches initial (input :: inputs) (output :: outputs) final ↔
      ∃ next,
        contract.CycleMatches input initial output next ∧
        contract.TraceMatches next inputs outputs final :=
  Execution.Trace.cons_iff

theorem TraceMatches.append
    {contract : ModuleResetContract ports}
    {initial middle final : contract.Synchronization}
    {leftInputs rightInputs : List ports.inputs.Values}
    {leftOutputs rightOutputs : List ports.outputs.Values}
    (left : contract.TraceMatches initial leftInputs leftOutputs middle)
    (right : contract.TraceMatches middle rightInputs rightOutputs final) :
    contract.TraceMatches initial (leftInputs ++ rightInputs)
      (leftOutputs ++ rightOutputs) final :=
  Execution.Trace.append left right

theorem TraceMatches.split
    {contract : ModuleResetContract ports}
    {initial final : contract.Synchronization}
    {leftInputs rightInputs : List ports.inputs.Values}
    {leftOutputs rightOutputs : List ports.outputs.Values}
    (trace : contract.TraceMatches initial (leftInputs ++ rightInputs)
      (leftOutputs ++ rightOutputs) final)
    (lengths : leftOutputs.length = leftInputs.length) :
    ∃ middle,
      contract.TraceMatches initial leftInputs leftOutputs middle ∧
      contract.TraceMatches middle rightInputs rightOutputs final :=
  Execution.Trace.split trace lengths

theorem TraceMatches.append_iff
    {contract : ModuleResetContract ports}
    {initial final : contract.Synchronization}
    {leftInputs rightInputs : List ports.inputs.Values}
    {leftOutputs rightOutputs : List ports.outputs.Values}
    (lengths : leftOutputs.length = leftInputs.length) :
    contract.TraceMatches initial (leftInputs ++ rightInputs)
        (leftOutputs ++ rightOutputs) final ↔
      ∃ middle,
        contract.TraceMatches initial leftInputs leftOutputs middle ∧
        contract.TraceMatches middle rightInputs rightOutputs final :=
  Execution.Trace.append_iff lengths

@[simp] theorem TraceMatches.cons_reset_iff
    {contract : ModuleResetContract ports} {initial final : contract.Synchronization}
    {input : ports.inputs.Values} {inputs : List ports.inputs.Values}
    {output : ports.outputs.Values} {outputs : List ports.outputs.Values}
    (asserted : contract.resetAsserted input = true) :
    contract.TraceMatches initial (input :: inputs) (output :: outputs) final ↔
      contract.TraceMatches (some contract.resetState) inputs outputs final := by
  rw [TraceMatches.cons_iff]
  constructor
  · rintro ⟨next, cycle, rest⟩
    have equal := (CycleMatches.reset_iff contract asserted).mp cycle
    cases equal
    exact rest
  · intro rest
    exact ⟨some contract.resetState, .reset asserted, rest⟩

@[simp] theorem TraceMatches.cons_beforeReset_iff
    {contract : ModuleResetContract ports} {final : contract.Synchronization}
    {input : ports.inputs.Values} {inputs : List ports.inputs.Values}
    {output : ports.outputs.Values} {outputs : List ports.outputs.Values}
    (notReset : contract.resetAsserted input = false) :
    contract.TraceMatches none (input :: inputs) (output :: outputs) final ↔
      contract.TraceMatches none inputs outputs final := by
  rw [TraceMatches.cons_iff]
  constructor
  · rintro ⟨next, cycle, rest⟩
    have equal := (CycleMatches.beforeReset_iff contract notReset).mp cycle
    cases equal
    exact rest
  · intro rest
    exact ⟨none, .beforeReset notReset, rest⟩

@[simp] theorem TraceMatches.cons_ordinary_iff
    {contract : ModuleResetContract ports} {state : contract.State}
    {final : contract.Synchronization} {input : ports.inputs.Values}
    {inputs : List ports.inputs.Values} {output : ports.outputs.Values}
    {outputs : List ports.outputs.Values}
    (notReset : contract.resetAsserted input = false) :
    contract.TraceMatches (some state) (input :: inputs)
        (output :: outputs) final ↔
      ports.outputs.Matches (contract.step input state).1 output ∧
        contract.TraceMatches (some (contract.step input state).2)
          inputs outputs final := by
  rw [TraceMatches.cons_iff]
  constructor
  · rintro ⟨next, cycle, rest⟩
    rcases (CycleMatches.ordinary_iff contract notReset).mp cycle with
      ⟨outputMatches, equal⟩
    cases equal
    exact ⟨outputMatches, rest⟩
  · rintro ⟨outputMatches, rest⟩
    exact ⟨some (contract.step input state).2,
      .ordinary notReset outputMatches, rest⟩

@[simp] theorem accepts_nil (contract : ModuleResetContract ports) :
    contract.Accepts [] [] :=
  ⟨none, .nil none⟩

theorem TraceMatches.before_first_reset
    (contract : ModuleResetContract ports) :
    ∀ {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values},
      outputs.length = inputs.length →
      (∀ input, input ∈ inputs → contract.resetAsserted input = false) →
      contract.TraceMatches none inputs outputs none
  | [], [], _, _ => .nil none
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | input :: inputs, output :: outputs, lengths, ordinary => by
      apply Execution.Trace.cons input output
      · exact .beforeReset (ordinary input (by simp))
      · apply TraceMatches.before_first_reset contract
        · simpa using lengths
        · intro tail member
          exact ordinary tail (by simp [member])

end ModuleResetContract

end Silean2
