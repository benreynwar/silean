import PicoRV.Authoring.CircuitLogic
import PicoRV.Datapath.Internal.DatapathBasicUpdatesStructure
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.VectorLayout.VectorLayout

/-! # Basic datapath update stages

These descriptions cover phase decoding and the small state-update layers used
by the complete datapath transition. They show only the fields owned by each
layer; expanded typed structures and certification remain under `Internal/`.
-/

namespace PicoRV.Datapath

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

namespace PhaseDecode.Description

noncomputable def construction : Builder Unit := do
  let state ← input "cpu_state" (.vector 8 .bit)
  let fetch ← Silean.Modules.EqualsConstant.place state (stateBits cpuStateFetch)
  let loadRs1 ← Silean.Modules.EqualsConstant.place state (stateBits cpuStateLdRs1)
  let loadRs2 ← Silean.Modules.EqualsConstant.place state (stateBits cpuStateLdRs2)
  let execute ← Silean.Modules.EqualsConstant.place state (stateBits cpuStateExec)
  let shift ← Silean.Modules.EqualsConstant.place state (stateBits cpuStateShift)
  let store ← Silean.Modules.EqualsConstant.place state (stateBits cpuStateStmem)
  let load ← Silean.Modules.EqualsConstant.place state (stateBits cpuStateLdmem)
  output "fetch" fetch
  output "loadRs1" loadRs1
  output "loadRs2" loadRs2
  output "execute" execute
  output "shift" shift
  output "store" store
  output "load" load

noncomputable def description : Description := build construction

end PhaseDecode.Description

namespace PhaseDecode

structure PlacedOutputs where
  fetch : Net .bit
  loadRs1 : Net .bit
  loadRs2 : Net .bit
  execute : Net .bit
  shift : Net .bit
  store : Net .bit
  load : Net .bit

noncomputable def placeNamed (name : Naming.SourceName)
    (state : Net (.vector 8 .bit)) : Builder PlacedOutputs := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .cpu_state => state
  pure ⟨child .fetch, child .loadRs1, child .loadRs2, child .execute,
    child .shift, child .store, child .load⟩

noncomputable def place (state : Net (.vector 8 .bit)) :
    Builder PlacedOutputs := do
  let child ← placeIndexed "datapath_phase_decode" design fun
    | .cpu_state => state
  pure ⟨child .fetch, child .loadRs1, child .loadRs2, child .execute,
    child .shift, child .store, child .load⟩

attribute [circuit_description] placeNamed place

end PhaseDecode

namespace Baseline.Description

noncomputable def construction : Builder Unit := do
  let current ← input "current" stateType
  let aluOut ← input "alu_out" (.vector 32 .bit)
  let fields ← split DatapathState.layout current
  output "state" (← update stateMap DatapathState.schema fields fun
    | .alu_out_q => some aluOut
    | _ => none)

noncomputable def description : Description := build construction

end Baseline.Description

namespace Baseline

noncomputable def placeNamed (name : Naming.SourceName)
    (current : Net stateType) (aluOut : Net (.vector 32 .bit)) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .current => current
    | .alu_out => aluOut
  pure (child .state)

noncomputable def place (current : Net stateType)
    (aluOut : Net (.vector 32 .bit)) : Builder (Net stateType) := do
  let child ← placeIndexed "datapath_baseline" design fun
    | .current => current
    | .alu_out => aluOut
  pure (child .state)

attribute [circuit_description] placeNamed place

end Baseline

namespace LoadRs2Update.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let _current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split DatapathInputs.layout inputs
  let updatedFields ← split DatapathState.layout updated
  let lowFive ← Silean.Modules.VectorLayout.place
    LoadRs2Update.lowFiveLayout (inputsFields .cpuregs_rs2)
  output "state" (← update stateMap DatapathState.schema updatedFields fun
    | .reg_op2 => some (inputsFields .cpuregs_rs2)
    | .reg_sh => some lowFive
    | _ => none)

noncomputable def description : Description := build construction

end LoadRs2Update.Description

namespace LoadRs2Update

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
  let child ← placeIndexed "datapath_load_rs2_update" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end LoadRs2Update

namespace ExecuteUpdate.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split DatapathInputs.layout inputs
  let currentFields ← split DatapathState.layout current
  let updatedFields ← split DatapathState.layout updated
  let target ← (currentFields .reg_pc) +ust (inputsFields .decoded_imm)
  output "state" (← update stateMap DatapathState.schema updatedFields fun
    | .reg_out => some target
    | _ => none)

noncomputable def description : Description := build construction

end ExecuteUpdate.Description

namespace ExecuteUpdate

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
  let child ← placeIndexed "datapath_execute_update" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end ExecuteUpdate

namespace ResetOverride.Description

noncomputable def construction : Builder Unit := do
  let resetn ← input "resetn" .bit
  let selected ← input "selected" stateType
  let fields ← split DatapathState.layout selected
  let zeroWord ← constant (.vector 32 .bit) (wordOfNat 0)
  let pc ← mux resetn zeroWord (fields .reg_pc)
  let nextPc ← mux resetn zeroWord (fields .reg_next_pc)
  output "state" (← update stateMap DatapathState.schema fields fun
    | .reg_pc => some pc
    | .reg_next_pc => some nextPc
    | _ => none)

noncomputable def description : Description := build construction

end ResetOverride.Description

namespace ResetOverride

noncomputable def placeNamed (name : Naming.SourceName)
    (resetn : Net .bit) (selected : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .resetn => resetn
    | .selected => selected
  pure (child .state)

noncomputable def place (resetn : Net .bit) (selected : Net stateType) :
    Builder (Net stateType) := do
  let child ← placeIndexed "datapath_reset_override" design fun
    | .resetn => resetn
    | .selected => selected
  pure (child .state)

attribute [circuit_description] placeNamed place

end ResetOverride

end PicoRV.Datapath
