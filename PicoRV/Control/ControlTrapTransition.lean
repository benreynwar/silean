import PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

namespace PicoRV.Control

open Silean
open Silean.Authoring

/-! Trap is deliberately a distinct phase child even though its state update
is small. It retains the complete baseline state and asserts only the
registered `trap` field. Keeping that behavior behind the common phase
boundary makes the parent phase selection uniform. -/

module_design TrapTransition (name := "picorv32_control_trap_transition") where
  boundary (PhaseTransition.ports) (naming := PhaseTransition.Naming.ports)
  instances {
    updatedFields := Silean.Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    trueBit := Silean.Modules.Constant.design .bit true,
    resultState := Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    falseBit := Silean.Modules.Constant.design .bit false,
    result := Silean.Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema }
  wiring {
  outputs { .transition := result.value }
  instance (.updatedFields) { .value := input.updated }
  instance (.trueBit) {}
  instance (.resultState) {
    .cpu_state := updatedFields[.cpu_state],
    .latched_store := updatedFields[.latched_store],
    .latched_stalu := updatedFields[.latched_stalu],
    .latched_branch := updatedFields[.latched_branch],
    .latched_is_lu := updatedFields[.latched_is_lu],
    .latched_is_lh := updatedFields[.latched_is_lh],
    .latched_is_lb := updatedFields[.latched_is_lb],
    .latched_rd := updatedFields[.latched_rd],
    .mem_wordsize := updatedFields[.mem_wordsize],
    .mem_do_prefetch := updatedFields[.mem_do_prefetch],
    .mem_do_rinst := updatedFields[.mem_do_rinst],
    .mem_do_rdata := updatedFields[.mem_do_rdata],
    .mem_do_wdata := updatedFields[.mem_do_wdata],
    .decoder_trigger := updatedFields[.decoder_trigger],
    .decoder_pseudo_trigger := updatedFields[.decoder_pseudo_trigger],
    .trap := trueBit.output }
  instance (.falseBit) {}
  instance (.result) {
    .state := resultState.value,
    .setRinst := falseBit.output,
    .setRdata := falseBit.output,
    .setWdata := falseBit.output }
  }

end PicoRV.Control
