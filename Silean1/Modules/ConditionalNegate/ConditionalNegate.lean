import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector
import Silean.Modules.AddWithCarry.AddWithCarryDerived
import Silean.Modules.Constant.Constant

/-! # Conditional fixed-width negation

`ConditionalNegate` either preserves a bit vector or applies native `BitVec`
two's-complement negation at the same width. This file contains only the public
boundary and natural contract; the hardware structure and its proof will be
added after that contract has been reviewed.
-/

namespace Silean.Modules.ConditionalNegate

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring

module_ports ports (width : Nat) where
  input value : .vector width .bit,
  input negate : .bit,
  output result : .vector width .bit

/-- The input unchanged, or its fixed-width two's-complement negation. -/
def resultValue (width : Nat) (value : Fin width → Bool) (negate : Bool) :
    Fin width → Bool :=
  bif negate then
    BitVector.ofBitVec (-BitVector.toBitVec width value)
  else
    value

module_cycle_contract cycleContract (width : Nat) for ports width where
  state := emptySignalMap
  output_rule apply where
    reads := [value, negate]
    writes := {
      result := resultValue width value negate }
  state_rule where
    reads := []
    next := {}

/-- An allowed step has the expected native fixed-width interpretation. -/
theorem result_toBitVec_of_allowed (width : Nat)
    {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step) :
    BitVector.toBitVec width (step.outputs .result) =
      bif step.inputs .negate then
        -BitVector.toBitVec width (step.inputs .value)
      else
        BitVector.toBitVec width (step.inputs .value) := by
  rw [cycleContract.result width allowed]
  cases negate : step.inputs .negate <;>
    simp [resultValue, negate]

/-- Broadcast shape used to present the control bit to every value bit. -/
def negateVector (width : Nat) : Composition.SignalCombiner :=
  .vector width .bit

open ports

/-- Readable XOR-plus-add implementation of fixed-width conditional
negation. -/
noncomputable def construction (width : Nat) : ModuleBuilder (ports width) Unit := do
  let value ← input width .value
  let negate ← input width .negate
  wire transformedValue ← value ^^^ (←
    combine (negateVector width) fun _ => negate)
  let zero ← constant (.vector width .bit) (fun _ => false)
  let added ← AddWithCarry.place transformedValue zero negate
  output width .result added.result

noncomputable def description (width : Nat) : Description :=
  ModuleBuilder.build (Naming.ports width) (construction width)

end Silean.Modules.ConditionalNegate
