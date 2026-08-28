import Silean.FIRRTL.Render
import Silean.Modules.SerialDepthFifo.SerialDepthFifoCertified

namespace Silean.Examples.Checks.SerialDepthFifo

open Silean Silean.Modules Silean.Naming Silean.FIRRTL

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

example : ModuleStructure (Silean.Interfaces.Fifo.ports payloadType) :=
  SerialDepthFifo.moduleStructure payloadType 1 (by omega)

example : ModuleStructure (Silean.Interfaces.Fifo.ports payloadType) :=
  SerialDepthFifo.moduleStructure payloadType 2 (by omega)

example : ModuleStructure (Silean.Interfaces.Fifo.ports payloadType) :=
  SerialDepthFifo.moduleStructure payloadType 3 (by omega)

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Silean.Interfaces.Fifo.ports payloadType) :=
  SerialDepthFifo.certified payloadType 3 (by omega)

def bitResetInputs : (Silean.Interfaces.Fifo.ports .bit).inputs.Values
  | .inputValid | .inputData | .outputReady => false
  | .reset => true

def fullBitState : (OneEntryFifo.stateMap .bit).Values
  | .storedValid | .storedData => true

def fullDepthTwoState :
    (SerialDepthFifo.cycleBehavior .bit 2 (by omega)).state.Values :=
  Contracts.Fifo.Cycle.combineState fullBitState fullBitState

example : Contracts.Fifo.Cycle.leftState
    ((SerialDepthFifo.cycleContract .bit 2 (by omega)).evaluate
      bitResetInputs fullDepthTwoState).2 .storedValid = false := rfl

example : Contracts.Fifo.Cycle.rightState
    ((SerialDepthFifo.cycleContract .bit 2 (by omega)).evaluate
      bitResetInputs fullDepthTwoState).2 .storedValid = false := rfl

example : (SerialDepthFifo.fifoCertified payloadType 3 (by omega)).contract.capacity = 3 := by
  rfl

example : (SerialDepthFifo.fifoCertified payloadType 3 (by omega)).moduleStructure.HasSolution :=
  (SerialDepthFifo.fifoCertified payloadType 3 (by omega)).hasSolution

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (result : RenderResult String) (fragments : List String) : Bool :=
  match result with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard containsAll
  (renderCircuit (SerialDepthFifo.Naming.depthNamingWith payloadType payloadNaming 3 (by omega)))
  ["public module serial_depth_fifo_structural_t_v3_bit_t_bit_v2_t_bit_bit_unit_unit_unit_3",
   "inst upstream of one_entry_fifo_structural_t_v3_bit_t_bit_v2_t_bit_bit_unit_unit_unit",
   "inst downstream of serial_depth_fifo_structural_t_v3_bit_t_bit_v2_t_bit_bit_unit_unit_unit_2",
   "a : UInt<1>[3]", "b : { c : UInt<1>, d : { e : UInt<1>, f : UInt<1> }[2] }"]

end Silean.Examples.Checks.SerialDepthFifo
