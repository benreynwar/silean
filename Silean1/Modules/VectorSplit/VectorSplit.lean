import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

/-! # Vector split

`VectorSplit` divides a vector into its low-index left portion and its
remaining right portion.
-/

namespace Silean.Modules.VectorSplit

open Silean
open Silean.Authoring

module_ports ports (element : SignalType) (leftWidth : Nat) (rightWidth : Nat)
    with (elementNaming : Naming.SignalTypeNaming element :=
      .positional element) where
  input value (schema := .vector elementNaming) :
    .vector (leftWidth + rightWidth) element,
  output left (schema := .vector elementNaming) : .vector leftWidth element,
  output right (schema := .vector elementNaming) : .vector rightWidth element

def leftPart (value : Fin (leftWidth + rightWidth) → α) : Fin leftWidth → α :=
  fun index => value (Fin.castAdd rightWidth index)

def rightPart (value : Fin (leftWidth + rightWidth) → α) : Fin rightWidth → α :=
  fun index => value (Fin.natAdd leftWidth index)

module_cycle_contract cycleContract (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat)
    for ports element leftWidth rightWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [value]
    writes := {
      left := leftPart value,
      right := rightPart value }
  state_rule where
    reads := []
    next := {}

/-- Every allowed step returns the two portions of its input. -/
theorem outputs_of_allowed (element : SignalType) (leftWidth rightWidth : Nat)
    {step : (cycleContract element leftWidth rightWidth).Step}
    (allowed : (cycleContract element leftWidth rightWidth).Allows step) :
    step.outputs .left = leftPart (step.inputs .value) ∧
      step.outputs .right = rightPart (step.inputs .value) :=
  ⟨cycleContract.left element leftWidth rightWidth allowed,
    cycleContract.right element leftWidth rightWidth allowed⟩

end Silean.Modules.VectorSplit
