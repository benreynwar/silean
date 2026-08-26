import Silean2.FIRRTL

namespace Silean2.Examples.FIRRTLChecks

open Silean2 Silean2.FIRRTL

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (result : RenderResult String) (fragments : List String) : Bool :=
  match result with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard containsAll BitMuxNaming.firrtl
  ["circuit mux_bit_gates", "public module mux_bit_gates",
   "inst choose_false of and_bit", "connect combine.left, choose_false.out"]

#guard containsAll (RegisterNaming.firrtl (.vector 2 .bit))
  ["public module register_structural_v2_bit",
   "reg stored : UInt<1>, clock", "connect register_component_0.clock, clock",
   "connect aggregate_0[1], component_1"]

#guard containsAll (EnabledRegisterNaming.firrtl (.tuple (.cons .bit (.cons .bit .nil))))
  ["public module enabled_register_structural_t_bit_bit_unit",
   "inst selection of mux_structural_t_bit_bit_unit",
   "connect storage.clock, clock", "{ _0 : UInt<1>, _1 : UInt<1> }"]

#guard containsAll (OneEntryFifoNaming.firrtl (.vector 2 .bit))
  ["public module one_entry_fifo_structural_v2_bit",
   "inst valid_storage of enabled_register_structural_bit",
   "inst data_storage of enabled_register_structural_v2_bit",
   "connect data_storage.clock, clock", "reg stored : UInt<1>, clock"]

end Silean2.Examples.FIRRTLChecks
