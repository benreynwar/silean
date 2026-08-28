import Silean.Foundation.DeriveEnumeration
import Silean.Foundation.ModulePorts
import Silean.Foundation.SignalSelection

namespace Silean.Contracts.Cycle

/-! # Exact one-cycle behavioral contracts

A `ModuleCycleContract` describes what a module does during one clock cycle,
independently of how the module is structurally implemented. Given the current
contract state and boundary inputs, it specifies every boundary output and the
complete next contract state.

Outputs are divided into named `CycleOutputRule`s. Each rule states exactly
which inputs it reads and which outputs it produces, making dependencies
available to structural certification. A single `CycleStateRule` describes the
clock-edge transition. Stateless modules use the same representation with an
empty state map.

The contract state is chosen for natural behavioral reasoning and need not be
the same as the state stored by the hardware hierarchy. Certification therefore
supplies a correspondence between contract state and structural state, proves
that every structural state has a corresponding contract state, and proves
that each cycle preserves the correspondence while producing the contract's
outputs. `CycleImplementation` defines this separate proof that a
`ModuleStructure` implements a contract. -/

/-! Output rules are the observable, dependency-aware pieces of a contract.
They read a selected set of module inputs, see complete current state, and
produce a selected set of module outputs. They contain no structure or order. -/

structure CycleOutputRuleShape where
  inputTypes : SignalTypes
  outputTypes : SignalTypes

def CycleOutputRuleShape.ofLists (inputTypes outputTypes : List SignalType) :
    CycleOutputRuleShape where
  inputTypes := .ofList inputTypes
  outputTypes := .ofList outputTypes

structure CycleOutputRule (ports : ModulePorts) (state : SignalMap)
    (shape : CycleOutputRuleShape) where
  /-- Module inputs required by this output rule. -/
  readsInputs : SignalSelection ports.inputs shape.inputTypes
  /-- Module outputs established by this rule. -/
  writesOutputs : SignalSelection ports.outputs shape.outputTypes
  /-- Computes those outputs from the selected inputs and complete current state. -/
  target : shape.inputTypes.Denote → state.Values →
    shape.outputTypes.Denote

abbrev SomeCycleOutputRule (ports : ModulePorts) (state : SignalMap) :=
  Sigma (CycleOutputRule ports state)

/-! Every contract has one clock-edge transition with precise selected input
dependencies and a complete next-state result. When its independent `state`
map is empty, both the input selection and result can be empty without
requiring a separate combinational contract type. -/

structure CycleStateRule (ports : ModulePorts) (state : SignalMap) where
  /-- Shapes of the module inputs needed for the transition. -/
  inputTypes : SignalTypes
  /-- Selects those inputs from the module boundary. -/
  readsInputs : SignalSelection ports.inputs inputTypes
  /-- Computes the complete next contract state. -/
  target : inputTypes.Denote → state.Values → state.Values

namespace CycleStateRule

def apply (rule : CycleStateRule ports state)
    (inputs : ports.inputs.Values) (currentState : state.Values) : state.Values :=
  rule.target (rule.readsInputs.project inputs) currentState

def empty (ports : ModulePorts) :
    CycleStateRule ports emptySignalMap where
  inputTypes := .nil
  readsInputs := .nil
  target := fun _ _ => SignalMap.emptyValues

@[simp] theorem empty_readsInputs_labels (ports : ModulePorts) :
    (empty ports).readsInputs.labels = [] := rfl

@[simp] theorem empty_apply (ports : ModulePorts)
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values) :
    (empty ports).apply inputs state = SignalMap.emptyValues := rfl

end CycleStateRule

/-! A contract owns a finite readable rule identity, its output rules, exact
output coverage, and the one complete state rule. The permutation says that the
concatenated write selections contain every output exactly once: the boundary
output enumeration is already duplicate-free. -/

structure ModuleCycleContract (ports : ModulePorts) where
  /-- Lean-friendly state used to describe behavior. -/
  state : SignalMap
  /-- Names the independently usable output rules. -/
  RuleName : Type
  /-- Finite enumeration of every output rule. -/
  ruleNames : Enumeration RuleName
  /-- Behavioral rule associated with each name. -/
  outputRule : RuleName → SomeCycleOutputRule ports state
  /-- The single complete clock-edge transition. -/
  stateRule : CycleStateRule ports state
  /-- Every boundary output is written exactly once across the output rules. -/
  outputCoverage :
    (ruleNames.values.flatMap fun name =>
      (outputRule name).2.writesOutputs.labels).Perm ports.outputs.labels.values

namespace ModuleCycleContract

def writtenOutputs (contract : ModuleCycleContract ports) : List ports.outputs.Label :=
  contract.ruleNames.values.flatMap fun name =>
    (contract.outputRule name).2.writesOutputs.labels

theorem writtenOutputs_perm (contract : ModuleCycleContract ports) :
    contract.writtenOutputs.Perm ports.outputs.labels.values :=
  contract.outputCoverage

theorem writtenOutputs_nodup (contract : ModuleCycleContract ports) :
    contract.writtenOutputs.Nodup :=
  contract.outputCoverage.nodup_iff.mpr ports.outputs.labels.nodup

theorem output_is_written (contract : ModuleCycleContract ports)
    (output : ports.outputs.Label) : output ∈ contract.writtenOutputs := by
  exact contract.outputCoverage.mem_iff.mpr
    (ListIndex.get_eq (ports.outputs.labels.locate output) ▸
      List.get_mem _ _)

end ModuleCycleContract

end Silean.Contracts.Cycle
