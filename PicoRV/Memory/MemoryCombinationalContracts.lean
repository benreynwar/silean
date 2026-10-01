import PicoRV.MemoryContract

namespace PicoRV.Memory

open Silean
open Silean.Authoring

namespace ReadFormatting

module_ports ports where
  input mem_wordsize : .vector 2 .bit,
  input reg_op1 : .vector 32 .bit,
  input mem_rdata : .vector 32 .bit,
  output mem_rdata_word : .vector 32 .bit

def outputValue (inputs : inputMap.Values) : Word :=
  formattedReadDataFrom (inputs .mem_wordsize) (inputs .reg_op1)
    (inputs .mem_rdata)

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := fun | .mem_rdata_word => outputValue inputs

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (inputs : inputMap.Values)
    (state : emptySignalMap.Values) (outputs : outputMap.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .mem_rdata_word = outputValue inputs := by
  simp only [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]
  constructor
  · intro equal; exact congrFun equal .mem_rdata_word
  · intro equal; funext output; cases output; exact equal

end ReadFormatting

namespace Response

module_ports ports where
  input resetn : .bit,
  input mem_do_rinst : .bit,
  input mem_do_rdata : .bit,
  input mem_do_wdata : .bit,
  input mem_ready : .bit,
  input mem_rdata : .vector 32 .bit,
  input current (schema := MemoryState.schema) : stateType,
  output mem_done : .bit,
  output mem_rdata_latched : .vector 32 .bit

def doneValue (resetn rinst rdata wdata ready : Bool)
    (current : stateType.Denote) : Bool :=
  memDoneFrom resetn rinst rdata wdata ready (stateMap.unpack current)

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule done where
    reads := [resetn, mem_do_rinst, mem_do_rdata, mem_do_wdata, mem_ready, current]
    writes := { mem_done := doneValue resetn mem_do_rinst mem_do_rdata
      mem_do_wdata mem_ready current }
  output_rule data where
    reads := [mem_ready, mem_rdata, current]
    writes := { mem_rdata_latched := memRdataLatchedFrom mem_ready mem_rdata
      (stateMap.unpack current) }
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

end Response

end PicoRV.Memory
