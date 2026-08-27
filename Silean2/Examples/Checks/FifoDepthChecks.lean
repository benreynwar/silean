import Silean2.FIRRTL.Render
import Silean2.Modules.FifoTemporal

namespace Silean2.Examples.Checks.FifoDepth

open Silean2 Silean2.Modules Silean2.Naming Silean2.FIRRTL
open Silean2.Contracts

def pairType : SignalType := .tuple (.cons .bit (.cons .bit .nil))
def bType : SignalType := .tuple (.cons .bit (.cons (.vector 2 pairType) .nil))
def payloadType : SignalType :=
  .tuple (.cons (.vector 3 .bit) (.cons bType .nil))

def pairNaming : SignalTypeNaming pairType :=
  .tuple (.cons "e" .bit (.cons "f" .bit .nil))
def bNaming : SignalTypeNaming bType :=
  .tuple (.cons "c" .bit (.cons "d" (.vector pairNaming) .nil))
def payloadNaming : SignalTypeNaming payloadType :=
  .tuple (.cons "a" (.vector .bit) (.cons "b" bNaming .nil))

example : ModuleStructure (OneEntryFifo.ports payloadType) :=
  Fifo.moduleStructure payloadType 1 (by omega)

example : ModuleStructure (OneEntryFifo.ports payloadType) :=
  Fifo.moduleStructure payloadType 2 (by omega)

example : ModuleStructure (OneEntryFifo.ports payloadType) :=
  Fifo.moduleStructure payloadType 3 (by omega)

noncomputable example : ModuleCycleCertified (OneEntryFifo.ports payloadType) :=
  Fifo.certified payloadType 3 (by omega)

example : (Fifo.Temporal.certifiedView payloadType 1 (by omega)).view.capacity = 1 := by
  simp

example : (Fifo.Temporal.certifiedView payloadType 2 (by omega)).view.capacity = 2 := by
  simp

example : (Fifo.Temporal.certifiedView payloadType 3 (by omega)).view.capacity = 3 := by
  simp

example : (Fifo.Temporal.certifiedView payloadType 3
    (by omega)).view.readyPropagationLatency = 0 := by
  simp

example : NoResetFifo.ModuleView.Satisfies
    (Fifo.Temporal.certifiedView payloadType 3 (by omega)).view
    (Fifo.Temporal.model (Fifo.behavior payloadType 3 (by omega))).executes :=
  (Fifo.Temporal.certifiedView payloadType 3 (by omega)).satisfies

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (result : RenderResult String) (fragments : List String) : Bool :=
  match result with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard containsAll
  (renderCircuit (Fifo.Naming.depthNamingWith payloadType payloadNaming 3 (by omega)))
  ["public module fifo_structural_t_v3_bit_t_bit_v2_t_bit_bit_unit_unit_unit_3",
   "inst upstream of one_entry_fifo_structural_t_v3_bit_t_bit_v2_t_bit_bit_unit_unit_unit",
   "inst downstream of fifo_structural_t_v3_bit_t_bit_v2_t_bit_bit_unit_unit_unit_2",
   "a : UInt<1>[3]", "b : { c : UInt<1>, d : { e : UInt<1>, f : UInt<1> }[2] }"]

end Silean2.Examples.Checks.FifoDepth
