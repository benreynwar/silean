import Silean.FIRRTL
import Silean.Modules.BitMux
import Silean.Modules.Register
import Silean.Modules.EnabledRegister
import Silean.Modules.OneEntryFifo.OneEntryFifo

namespace Silean.Examples.Checks.FIRRTL

open Silean Silean.FIRRTL

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (result : RenderResult String) (fragments : List String) : Bool :=
  match result with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard containsAll (renderCircuit Modules.BitMux.Naming.naming)
  ["circuit mux_bit_gates", "public module mux_bit_gates",
   "inst choose_false of and_bit", "connect combine.left, choose_false.out"]

#guard containsAll (renderCircuit (Modules.Register.Naming.naming (.vector 2 .bit)))
  ["public module register_structural_v2_bit",
   "reg stored : UInt<1>, clock", "connect register_component_0.clock, clock",
   "connect aggregate_0[1], component_1"]

#guard containsAll (renderCircuit
  (Modules.EnabledRegister.Naming.naming (.tuple (.cons .bit (.cons .bit .nil)))))
  ["public module enabled_register_structural_t_bit_bit_unit",
   "inst selection of mux_structural_t_bit_bit_unit",
   "connect storage.clock, clock", "{ _0 : UInt<1>, _1 : UInt<1> }"]

#guard containsAll (renderCircuit (Modules.OneEntryFifo.Naming.naming (.vector 2 .bit)))
  ["public module one_entry_fifo_structural_v2_bit",
   "inst valid_storage of enabled_reset_register_structural_bit_0",
   "inst data_storage of enabled_register_structural_v2_bit",
   "connect valid_storage.reset, reset",
   "connect data_storage.clock, clock", "reg stored : UInt<1>, clock"]

end Silean.Examples.Checks.FIRRTL
