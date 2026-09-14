import Silean.Authoring.ModuleCycleContract
import Silean.Modules.Mux.MuxStructure

namespace Silean.Modules.Mux

open Silean
open Silean.Authoring

/-! ## Exact cycle behavior -/

module_cycle_contract cycleContract (signalType : SignalType)
    for ports signalType where
  state := emptySignalMap
  output_rule select where
    reads := [select, whenFalse, whenTrue]
    writes := {
      result := bif select then whenTrue else whenFalse }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.Mux
