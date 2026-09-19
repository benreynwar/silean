import PicoRV.Control.Internal.ControlAlignmentStructure
import PicoRV.Authoring.CircuitLogic
import Silean.Modules.EqualsConstant.EqualsConstant

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Control-address alignment

Misalignment is determined entirely by the current request, its word size, and
the low address bits. The description intentionally exposes those low-bit
tests rather than implementing division or remainder hardware. The expanded
typed hierarchy and verification remain under `Internal/`. -/

namespace Alignment.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let inputsFields ← split ControlInputs.layout inputs
  let stateFields ← split ControlState.layout current
  let op1Bits ← splitVector 32 .bit (inputsFields .reg_op1)
  let pcBits ← splitVector 32 .bit (inputsFields .reg_pc)
  let sizeIsWord ← Silean.Modules.EqualsConstant.place
    (stateFields .mem_wordsize) (twoBitsOfNat 0)
  let sizeIsHalf ← Silean.Modules.EqualsConstant.place
    (stateFields .mem_wordsize) (twoBitsOfNat 1)
  let dataCommand ← stateFields .mem_do_rdata ||| stateFields .mem_do_wdata
  let op1Low ← op1Bits 0 ||| op1Bits 1
  let pcLow ← pcBits 0 ||| pcBits 1
  let wordMisaligned ← sizeIsWord &&& op1Low
  let halfMisaligned ← sizeIsHalf &&& op1Bits 0
  let sizeMisaligned ← wordMisaligned ||| halfMisaligned
  output "data" (← dataCommand &&& sizeMisaligned)
  output "instruction" (← stateFields .mem_do_rinst &&& pcLow)

noncomputable def description : Description := build construction

end Alignment.Description

namespace Alignment

structure PlacedOutputs where
  data : Net .bit
  instruction : Net .bit

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current : Net stateType) :
    Builder PlacedOutputs := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
  pure { data := child .data, instruction := child .instruction }

noncomputable def place (inputs : Net inputsType) (current : Net stateType) :
    Builder PlacedOutputs := do
  let child ← placeIndexed "alignment" design fun
    | .inputs => inputs
    | .current => current
  pure { data := child .data, instruction := child .instruction }

attribute [circuit_description] placeNamed place

end Alignment

end PicoRV.Control
