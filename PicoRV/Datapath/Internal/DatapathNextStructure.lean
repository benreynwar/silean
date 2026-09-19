import PicoRV.Datapath.DatapathBasicUpdates
import PicoRV.Datapath.DatapathFetchUpdate
import PicoRV.Datapath.DatapathLoadRs1Update
import PicoRV.Datapath.DatapathMemoryUpdate
import PicoRV.Datapath.DatapathShiftUpdate
import Silean.Authoring.ModuleDesign
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

namespace PicoRV.Datapath

open Silean
open Silean.Authoring

/-! Complete combinational datapath transition. Phase selection follows the
source order and is total over arbitrary eight-bit values; an unknown phase
retains the ALU-capture baseline. Reset overrides only the two PC fields after
that selection. -/
module_design Next (name := "picorv32_datapath_next") where
  boundary (Next.ports) (naming := Next.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      DatapathInputs.signalMap DatapathInputs.schema,
    baseline (name := .indexed "datapath_baseline" 0) := Baseline.design,
    phaseDecode (name := .indexed "datapath_phase_decode" 0) := PhaseDecode.design,
    fetch (name := .indexed "datapath_fetch_update" 0) := FetchUpdate.design,
    loadRs1 (name := .indexed "datapath_load_rs1_update" 0) := LoadRs1Update.design,
    loadRs2 (name := .indexed "datapath_load_rs2_update" 0) := LoadRs2Update.design,
    execute (name := .indexed "datapath_execute_update" 0) := ExecuteUpdate.design,
    shift (name := .indexed "datapath_shift_update" 0) := ShiftUpdate.design,
    store (name := .indexed "datapath_store_update" 0) := StoreUpdate.design,
    load (name := .indexed "datapath_load_update" 0) := LoadUpdate.design,
    selectLoad (name := .indexed "mux" 0) := Silean.Modules.Mux.design stateType,
    selectStore (name := .indexed "mux" 1) := Silean.Modules.Mux.design stateType,
    selectShift (name := .indexed "mux" 2) := Silean.Modules.Mux.design stateType,
    selectExecute (name := .indexed "mux" 3) := Silean.Modules.Mux.design stateType,
    selectLoadRs2 (name := .indexed "mux" 4) := Silean.Modules.Mux.design stateType,
    selectLoadRs1 (name := .indexed "mux" 5) := Silean.Modules.Mux.design stateType,
    selectFetch (name := .indexed "mux" 6) := Silean.Modules.Mux.design stateType,
    resetOverride (name := .indexed "datapath_reset_override" 0) := ResetOverride.design }
  wiring {
  outputs { .state := resetOverride.state }
  instance (.inputsFields) { .value := input.inputs }
  instance (.baseline) { .current := input.current, .alu_out := input.alu_out }
  instance (.phaseDecode) { .cpu_state := inputsFields[.cpu_state] }
  instance (.fetch) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.loadRs1) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.loadRs2) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.execute) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.shift) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.store) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.load) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.selectLoad) {
    .select := phaseDecode.load,
    .whenFalse := baseline.state,
    .whenTrue := load.state }
  instance (.selectStore) {
    .select := phaseDecode.store,
    .whenFalse := selectLoad.result,
    .whenTrue := store.state }
  instance (.selectShift) {
    .select := phaseDecode.shift,
    .whenFalse := selectStore.result,
    .whenTrue := shift.state }
  instance (.selectExecute) {
    .select := phaseDecode.execute,
    .whenFalse := selectShift.result,
    .whenTrue := execute.state }
  instance (.selectLoadRs2) {
    .select := phaseDecode.loadRs2,
    .whenFalse := selectExecute.result,
    .whenTrue := loadRs2.state }
  instance (.selectLoadRs1) {
    .select := phaseDecode.loadRs1,
    .whenFalse := selectLoadRs2.result,
    .whenTrue := loadRs1.state }
  instance (.selectFetch) {
    .select := phaseDecode.fetch,
    .whenFalse := selectLoadRs1.result,
    .whenTrue := fetch.state }
  instance (.resetOverride) {
    .resetn := inputsFields[.resetn],
    .selected := selectFetch.result }
  }

end PicoRV.Datapath
