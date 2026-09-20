import PicoRV.Authoring.CircuitLogic
import PicoRV.Datapath.Internal.DatapathFetchUpdateStructure
import Silean.Modules.Add.AddDerived
import Silean.Modules.VectorLayout.VectorLayout

namespace PicoRV.Datapath

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

/-! # Fetch datapath update

Fetch first commits the prospective PC, optionally selecting the aligned
registered branch target. A current decoder trigger then computes the following
sequential or JAL PC from that same selected current PC. -/

namespace FetchUpdate.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split DatapathInputs.layout inputs
  let currentFields ← split DatapathState.layout current
  let updatedFields ← split DatapathState.layout updated
  let falseBit ← constant .bit false
  let four ← constant (.vector 32 .bit) (wordOfNat 4)
  let branchStored ← inputsFields .latched_branch &&& inputsFields .latched_store
  let branchSource ← mux (inputsFields .latched_stalu)
    (currentFields .reg_out) (currentFields .alu_out_q)
  let alignedBranch ← Silean.Modules.VectorLayout.place
    FetchUpdate.clearLowLayout branchSource
  let currentPc ← mux branchStored (currentFields .reg_next_pc) alignedBranch
  let sequentialPc ← Silean.Modules.Add.place currentPc four falseBit
  let jalPc ← Silean.Modules.Add.place
    currentPc (inputsFields .decoded_imm_j) falseBit
  let decodedPc ← mux (inputsFields .instr_jal)
    sequentialPc.result jalPc.result
  let nextPc ← mux (inputsFields .decoder_trigger) currentPc decodedPc
  output "state" (← update stateMap DatapathState.schema updatedFields fun
    | .reg_pc => some currentPc
    | .reg_next_pc => some nextPc
    | _ => none)

noncomputable def description : Description := build construction

end FetchUpdate.Description

namespace FetchUpdate

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
  let child ← placeIndexed "datapath_fetch_update" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end FetchUpdate

end PicoRV.Datapath
