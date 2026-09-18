import PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.BitMux.BitMux
import Silean.Modules.Constant.Constant
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

namespace PicoRV.Control

open Silean
open Silean.Authoring

/-! Shift always marks a pending register write. Only an exactly zero
five-bit shift count returns to fetch and promotes prefetch to instruction
read; a nonzero count retains both the phase and the existing read command. -/

module_design ShiftTransition (name := "picorv32_control_shift_transition") where
  boundary (PhaseTransition.ports) (naming := PhaseTransition.Naming.ports)
  instances {
    inputsFields := Silean.Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    updatedFields := Silean.Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    falseBit := Silean.Modules.Constant.design .bit false,
    trueBit := Silean.Modules.Constant.design .bit true,
    fetchState := Silean.Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateFetch),
    shiftIsZero := Silean.Modules.EqualsConstant.design (.vector 5 .bit)
      (fiveBitsOfNat 0),
    selectedPhase := Silean.Modules.Mux.design (.vector 8 .bit),
    selectedRinst := Silean.Modules.BitMux.design,
    resultState := Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    result := Silean.Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema }
  wiring {
  outputs { .transition := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.updatedFields) { .value := input.updated }
  instance (.falseBit) {}
  instance (.trueBit) {}
  instance (.fetchState) {}
  instance (.shiftIsZero) { .value := inputsFields[.reg_sh] }
  instance (.selectedPhase) {
    .select := shiftIsZero.result,
    .whenFalse := updatedFields[.cpu_state],
    .whenTrue := fetchState.output }
  instance (.selectedRinst) {
    .select := shiftIsZero.result,
    .whenFalse := updatedFields[.mem_do_rinst],
    .whenTrue := updatedFields[.mem_do_prefetch] }
  instance (.resultState) {
    .cpu_state := selectedPhase.result,
    .latched_store := trueBit.output,
    .latched_stalu := updatedFields[.latched_stalu],
    .latched_branch := updatedFields[.latched_branch],
    .latched_is_lu := updatedFields[.latched_is_lu],
    .latched_is_lh := updatedFields[.latched_is_lh],
    .latched_is_lb := updatedFields[.latched_is_lb],
    .latched_rd := updatedFields[.latched_rd],
    .mem_wordsize := updatedFields[.mem_wordsize],
    .mem_do_prefetch := updatedFields[.mem_do_prefetch],
    .mem_do_rinst := selectedRinst.result,
    .mem_do_rdata := updatedFields[.mem_do_rdata],
    .mem_do_wdata := updatedFields[.mem_do_wdata],
    .decoder_trigger := updatedFields[.decoder_trigger],
    .decoder_pseudo_trigger := updatedFields[.decoder_pseudo_trigger],
    .trap := updatedFields[.trap] }
  instance (.result) {
    .state := resultState.value,
    .setRinst := falseBit.output,
    .setRdata := falseBit.output,
    .setWdata := falseBit.output }
  }

end PicoRV.Control
