import PicoRV.Authoring.CircuitLogic
import PicoRV.Datapath.DatapathBasicUpdates
import PicoRV.Datapath.DatapathFetchUpdate
import PicoRV.Datapath.DatapathLoadRs1Update
import PicoRV.Datapath.DatapathMemoryUpdate
import PicoRV.Datapath.DatapathShiftUpdate
import PicoRV.Datapath.Internal.DatapathNextStructure

namespace PicoRV.Datapath

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring

/-! # Complete datapath-state update

Every phase candidate starts from the ALU-capture baseline. The old CPU phase
then selects one candidate in source priority order; an unknown phase retains
the baseline. Reset overrides only the two PC fields after that selection. -/

namespace Next.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let aluOut ← input "alu_out" (.vector 32 .bit)
  let inputsFields ← split DatapathInputs.layout inputs
  let baseline ← Baseline.place current aluOut
  let phase ← PhaseDecode.place (inputsFields .cpu_state)
  let fetch ← FetchUpdate.place inputs current baseline
  let loadRs1 ← LoadRs1Update.place inputs current baseline
  let loadRs2 ← LoadRs2Update.place inputs current baseline
  let execute ← ExecuteUpdate.place inputs current baseline
  let shift ← ShiftUpdate.place inputs current baseline
  let store ← StoreUpdate.place inputs current baseline
  let load ← LoadUpdate.place inputs current baseline
  let selected ← mux phase.load baseline load
  let selected ← mux phase.store selected store
  let selected ← mux phase.shift selected shift
  let selected ← mux phase.execute selected execute
  let selected ← mux phase.loadRs2 selected loadRs2
  let selected ← mux phase.loadRs1 selected loadRs1
  let selected ← mux phase.fetch selected fetch
  output "state" (← ResetOverride.place (inputsFields .resetn) selected)

noncomputable def description : Description := build construction

end Next.Description

namespace Next

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current : Net stateType)
    (aluOut : Net (.vector 32 .bit)) : Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .alu_out => aluOut
  pure (child .state)

noncomputable def place (inputs : Net inputsType) (current : Net stateType)
    (aluOut : Net (.vector 32 .bit)) : Builder (Net stateType) := do
  let child ← placeIndexed "datapath_next" design fun
    | .inputs => inputs
    | .current => current
    | .alu_out => aluOut
  pure (child .state)

attribute [circuit_description] placeNamed place

end Next

end PicoRV.Datapath
