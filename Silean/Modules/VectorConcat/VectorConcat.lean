import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

/-! # Vector concatenation

`VectorConcat` joins two vectors of the same element type, placing the left
vector at the lower result indices.
-/

namespace Silean.Modules.VectorConcat

open Silean
open Silean.Authoring

module_ports ports (element : SignalType) (leftWidth : Nat) (rightWidth : Nat)
    with (elementNaming : Naming.SignalTypeNaming element :=
      .positional element) where
  input left (schema := .vector elementNaming) : .vector leftWidth element,
  input right (schema := .vector elementNaming) : .vector rightWidth element,
  output result (schema := .vector elementNaming) :
    .vector (leftWidth + rightWidth) element

def concat (left : Fin leftWidth → α) (right : Fin rightWidth → α) :
    Fin (leftWidth + rightWidth) → α :=
  Fin.addCases left right

@[simp] theorem concat_left (left : Fin leftWidth → α)
    (right : Fin rightWidth → α) (index : Fin leftWidth) :
    concat left right (Fin.castAdd rightWidth index) = left index := by
  simp [concat]

@[simp] theorem concat_right (left : Fin leftWidth → α)
    (right : Fin rightWidth → α) (index : Fin rightWidth) :
    concat left right (Fin.natAdd leftWidth index) = right index := by
  simp [concat]

module_cycle_contract cycleContract (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat)
    for ports element leftWidth rightWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [left, right]
    writes := { result := concat left right }
  state_rule where
    reads := []
    next := {}

theorem result_left_of_allowed (element : SignalType) (leftWidth rightWidth : Nat)
    {step : (cycleContract element leftWidth rightWidth).Step}
    (allowed : (cycleContract element leftWidth rightWidth).Allows step)
    (index : Fin leftWidth) :
    step.outputs .result (Fin.castAdd rightWidth index) =
      step.inputs .left index := by
  rw [cycleContract.result element leftWidth rightWidth allowed]
  exact concat_left _ _ index

theorem result_right_of_allowed (element : SignalType) (leftWidth rightWidth : Nat)
    {step : (cycleContract element leftWidth rightWidth).Step}
    (allowed : (cycleContract element leftWidth rightWidth).Allows step)
    (index : Fin rightWidth) :
    step.outputs .result (Fin.natAdd leftWidth index) =
      step.inputs .right index := by
  rw [cycleContract.result element leftWidth rightWidth allowed]
  exact concat_right _ _ index

end Silean.Modules.VectorConcat
