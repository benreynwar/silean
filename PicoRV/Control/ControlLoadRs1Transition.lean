import PicoRV.Control.Internal.ControlLoadRs1TransitionStructure
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Load-RS1 transition

Load-RS1 is an ordered decoder, not a one-hot selection. The paired mux chains
make that priority visible for both fields they may change: `cpu_state` and
`mem_do_rinst`. This matters for arbitrary overlapping decoder inputs, which
the universal contract does not rule out. The expanded typed hierarchy and
verification remain under `Internal/`. -/

namespace LoadRs1Transition.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  discard (input "current" stateType)
  let updated ← input "updated" stateType
  let inputsFields ← split ControlInputs.layout inputs
  let updatedFields ← split ControlState.layout updated
  let falseBit ← constant .bit false
  let trueBit ← constant .bit true
  let trapState ← constant (.vector 8 .bit) (stateBits cpuStateTrap)
  let executeState ← constant (.vector 8 .bit) (stateBits cpuStateExec)
  let loadState ← constant (.vector 8 .bit) (stateBits cpuStateLdmem)
  let shiftState ← constant (.vector 8 .bit) (stateBits cpuStateShift)
  let storeState ← constant (.vector 8 .bit) (stateBits cpuStateStmem)

  let regShiftPhase ← mux (inputsFields .is_sll_srl_sra)
    executeState shiftState
  let regShiftRinst ← mux (inputsFields .is_sll_srl_sra)
    (updatedFields .mem_do_prefetch) (updatedFields .mem_do_rinst)
  let storePhase ← mux (inputsFields .is_sb_sh_sw)
    regShiftPhase storeState
  let storeRinst ← mux (inputsFields .is_sb_sh_sw)
    regShiftRinst trueBit
  let immediateAluPhase ← mux
    (inputsFields .is_jalr_addi_slti_sltiu_xori_ori_andi)
    storePhase executeState
  let immediateAluRinst ← mux
    (inputsFields .is_jalr_addi_slti_sltiu_xori_ori_andi)
    storeRinst (updatedFields .mem_do_prefetch)
  let immediateShiftPhase ← mux (inputsFields .is_slli_srli_srai)
    immediateAluPhase shiftState
  let immediateShiftRinst ← mux (inputsFields .is_slli_srli_srai)
    immediateAluRinst (updatedFields .mem_do_rinst)
  let loadPhase ← mux (inputsFields .is_lb_lh_lw_lbu_lhu)
    immediateShiftPhase loadState
  let loadRinst ← mux (inputsFields .is_lb_lh_lw_lbu_lhu)
    immediateShiftRinst trueBit
  let directPhase ← mux (inputsFields .is_lui_auipc_jal)
    loadPhase executeState
  let directRinst ← mux (inputsFields .is_lui_auipc_jal)
    loadRinst (updatedFields .mem_do_prefetch)
  let trapPhase ← mux (inputsFields .instr_trap)
    directPhase trapState
  let trapRinst ← mux (inputsFields .instr_trap)
    directRinst (updatedFields .mem_do_rinst)

  let resultState ← update stateMap ControlState.schema
    updatedFields fun
      | .cpu_state => some trapPhase
      | .mem_do_rinst => some trapRinst
      | _ => none
  let result ← combine TransitionValue.signalMap
    TransitionValue.schema fun
      | .state => resultState
      | .setRinst | .setRdata | .setWdata => falseBit
  output "transition" result

noncomputable def description : Description := build construction

end LoadRs1Transition.Description

namespace LoadRs1Transition

structure PlacedOutputs where
  transition : Net transitionType

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current updated : Net stateType) :
    Builder PlacedOutputs := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

noncomputable def place (inputs : Net inputsType)
    (current updated : Net stateType) : Builder PlacedOutputs := do
  let child ← placeIndexed "load_rs1_transition" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

attribute [circuit_description] placeNamed place

end LoadRs1Transition

end PicoRV.Control
