import PicoRV.Authoring.CircuitLogic
import PicoRV.Datapath.Internal.DatapathMemoryUpdateStructure
import Silean.Modules.VectorLayout.VectorLayout

namespace PicoRV.Datapath

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Load/store datapath update

The shared core computes the effective address while a request is active and
captures formatted load data when a load completes. `StoreUpdate` and
`LoadUpdate` are thin constant specializations of that circuit. -/

namespace MemoryUpdateCore.Description

noncomputable def construction : Builder Unit := do
  let isLoad ← input "isLoad" .bit
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split DatapathInputs.layout inputs
  let currentFields ← split DatapathState.layout current
  let updatedFields ← split DatapathState.layout updated
  let zeroWord ← constant (.vector 32 .bit) (wordOfNat 0)
  let notPrefetch ← !! (inputsFields .mem_do_prefetch)
  let progress ← notPrefetch ||| inputsFields .mem_done
  let active ← mux isLoad
    (inputsFields .mem_do_wdata) (inputsFields .mem_do_rdata)
  let notActive ← !! active
  let effectiveAddress ←
    (currentFields .reg_op1) +ust (inputsFields .decoded_imm)
  let effectiveOp1 ← mux notActive
    (updatedFields .reg_op1) effectiveAddress
  let selectedOp1 ← mux progress (updatedFields .reg_op1) effectiveOp1
  let signedHalf ← Silean.Modules.VectorLayout.place
    (MemoryUpdateCore.signExtendLayout 16) (inputsFields .mem_rdata_word)
  let signedByte ← Silean.Modules.VectorLayout.place
    (MemoryUpdateCore.signExtendLayout 8) (inputsFields .mem_rdata_word)
  let loadValue ← mux (inputsFields .latched_is_lb) zeroWord signedByte
  let loadValue ← mux (inputsFields .latched_is_lh) loadValue signedHalf
  let loadValue ← mux (inputsFields .latched_is_lu)
    loadValue (inputsFields .mem_rdata_word)
  let loadDone ← isLoad &&& notPrefetch
  let loadDone ← loadDone &&& inputsFields .mem_done
  let selectedResult ← mux loadDone (updatedFields .reg_out) loadValue
  output "state" (← update stateMap DatapathState.schema updatedFields fun
    | .reg_op1 => some selectedOp1
    | .reg_out => some selectedResult
    | _ => none)

noncomputable def description : Description := build construction

end MemoryUpdateCore.Description

namespace MemoryUpdateCore

noncomputable def placeNamed (name : Naming.SourceName)
    (isLoad : Net .bit) (inputs : Net inputsType)
    (current updated : Net stateType) : Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .isLoad => isLoad
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

noncomputable def place (isLoad : Net .bit) (inputs : Net inputsType)
    (current updated : Net stateType) : Builder (Net stateType) := do
  let child ← placeIndexed "datapath_memory_update" design fun
    | .isLoad => isLoad
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end MemoryUpdateCore

namespace StoreUpdate.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
  let isLoad ← constant .bit false
  output "state" (← MemoryUpdateCore.place isLoad inputs current updated)

noncomputable def description : Description := build construction

end StoreUpdate.Description

namespace StoreUpdate

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
  let child ← placeIndexed "datapath_store_update" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end StoreUpdate

namespace LoadUpdate.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
  let isLoad ← constant .bit true
  output "state" (← MemoryUpdateCore.place isLoad inputs current updated)

noncomputable def description : Description := build construction

end LoadUpdate.Description

namespace LoadUpdate

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
  let child ← placeIndexed "datapath_load_update" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end LoadUpdate

end PicoRV.Datapath
