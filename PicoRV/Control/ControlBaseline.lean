import PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming

namespace PicoRV.Control

open Silean
open Silean.Authoring

/-! The baseline layer represents the unconditional assignments at the start
of the source control block. Every state field passes through except `trap`
and `decoder_pseudo_trigger`, which clear, and `decoder_trigger`, which records
completion of the current instruction fetch. Later phase children deliberately
receive this result rather than the raw state. -/

module_design Baseline (name := "picorv32_control_baseline") where
  boundary (Baseline.ports) (naming := Baseline.Naming.ports)
  instances {
    inputsFields := Silean.Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    currentFields := Silean.Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    falseBit := Silean.Modules.Constant.design .bit false,
    fetchCompleted := Silean.Primitives.andDesign,
    result := Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.falseBit) {}
  instance (.fetchCompleted) {
    .left := currentFields[.mem_do_rinst],
    .right := inputsFields[.mem_done] }
  instance (.result) {
    .cpu_state := currentFields[.cpu_state],
    .latched_store := currentFields[.latched_store],
    .latched_stalu := currentFields[.latched_stalu],
    .latched_branch := currentFields[.latched_branch],
    .latched_is_lu := currentFields[.latched_is_lu],
    .latched_is_lh := currentFields[.latched_is_lh],
    .latched_is_lb := currentFields[.latched_is_lb],
    .latched_rd := currentFields[.latched_rd],
    .mem_wordsize := currentFields[.mem_wordsize],
    .mem_do_prefetch := currentFields[.mem_do_prefetch],
    .mem_do_rinst := currentFields[.mem_do_rinst],
    .mem_do_rdata := currentFields[.mem_do_rdata],
    .mem_do_wdata := currentFields[.mem_do_wdata],
    .decoder_trigger := fetchCompleted.output,
    .decoder_pseudo_trigger := falseBit.output,
    .trap := falseBit.output }
  }

end PicoRV.Control
