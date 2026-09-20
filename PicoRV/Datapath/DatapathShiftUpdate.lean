import PicoRV.Authoring.CircuitLogic
import PicoRV.Datapath.Internal.DatapathShiftUpdateStructure
import Silean.Modules.AddSub.AddSubDerived
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.VectorLayout.VectorLayout

namespace PicoRV.Datapath

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

/-! # Iterative shift update

Amount zero finishes by copying the current operand to `reg_out`. Otherwise a
step shifts by four when any high count bit is set and by one when not, then
subtracts the same amount from the remaining count. The operation selection
retains the source priority: arithmetic right, logical right, then left. -/

namespace ShiftUpdate.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split DatapathInputs.layout inputs
  let currentFields ← split DatapathState.layout current
  let updatedFields ← split DatapathState.layout updated
  let amountBits ← splitVector 5 .bit (currentFields .reg_sh)
  let amountHigh ← amountBits 2 ||| amountBits 3
  let amountGeFour ← amountHigh ||| amountBits 4
  let amountZero ← Silean.Modules.EqualsConstant.place
    (currentFields .reg_sh) (fiveBitsOfNat 0)
  let leftSelect ← inputsFields .instr_slli ||| inputsFields .instr_sll
  let logicalSelect ← inputsFields .instr_srli ||| inputsFields .instr_srl
  let arithmeticSelect ← inputsFields .instr_srai ||| inputsFields .instr_sra
  let trueBit ← constant .bit true
  let leftOne ← Silean.Modules.VectorLayout.place
    (ShiftUpdate.leftLayout 1) (currentFields .reg_op1)
  let leftFour ← Silean.Modules.VectorLayout.place
    (ShiftUpdate.leftLayout 4) (currentFields .reg_op1)
  let logicalOne ← Silean.Modules.VectorLayout.place
    (ShiftUpdate.rightLogicalLayout 1) (currentFields .reg_op1)
  let logicalFour ← Silean.Modules.VectorLayout.place
    (ShiftUpdate.rightLogicalLayout 4) (currentFields .reg_op1)
  let arithmeticOne ← Silean.Modules.VectorLayout.place
    (ShiftUpdate.rightArithmeticLayout 1) (currentFields .reg_op1)
  let arithmeticFour ← Silean.Modules.VectorLayout.place
    (ShiftUpdate.rightArithmeticLayout 4) (currentFields .reg_op1)
  let selectedLeft ← mux amountGeFour leftOne leftFour
  let selectedLogical ← mux amountGeFour logicalOne logicalFour
  let selectedArithmetic ← mux amountGeFour arithmeticOne arithmeticFour
  let shifted ← mux arithmeticSelect
    (currentFields .reg_op1) selectedArithmetic
  let shifted ← mux logicalSelect shifted selectedLogical
  let shifted ← mux leftSelect shifted selectedLeft
  let one ← constant (.vector 5 .bit) (fiveBitsOfNat 1)
  let four ← constant (.vector 5 .bit) (fiveBitsOfNat 4)
  let selectedStep ← mux amountGeFour one four
  let remaining ← Silean.Modules.AddSub.place
    (currentFields .reg_sh) selectedStep trueBit
  let selectedOp1 ← mux amountZero shifted (updatedFields .reg_op1)
  let selectedShift ← mux amountZero remaining.result (updatedFields .reg_sh)
  let selectedResult ← mux amountZero
    (updatedFields .reg_out) (currentFields .reg_op1)
  output "state" (← update stateMap DatapathState.schema updatedFields fun
    | .reg_op1 => some selectedOp1
    | .reg_out => some selectedResult
    | .reg_sh => some selectedShift
    | _ => none)

noncomputable def description : Description := build construction

end ShiftUpdate.Description

namespace ShiftUpdate

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current updated : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

noncomputable def place (inputs : Net inputsType)
    (current updated : Net stateType) : Builder (Net stateType) := do
  let child ← placeIndexed "datapath_shift_update" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end ShiftUpdate

end PicoRV.Datapath
