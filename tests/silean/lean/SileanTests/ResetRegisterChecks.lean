import Silean.FIRRTL
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterDerived

namespace SileanTests.ResetRegister

open Silean
open Silean.FIRRTL
open Silean.Naming

def resetBitInputs (value reset : Bool) :
    (Modules.ResetRegister.ports .bit).inputs.Values
  | .value => value
  | .reset => reset

def enabledBitInputs (value enable reset : Bool) :
    (Modules.EnabledResetRegister.ports .bit).inputs.Values
  | .value => value
  | .enable => enable
  | .reset => reset

def bitState (stored : Bool) : (Modules.Register.stateMap .bit).Values
  | .stored => stored

def resetBitNext (value reset stored : Bool) : Bool :=
  ((Modules.ResetRegister.cycleContract .bit false).evaluate
    (resetBitInputs value reset) (bitState stored)).2 .stored

#guard resetBitNext true false false
#guard !(resetBitNext true true true)

def enabledBitNext (value enable reset stored : Bool) : Bool :=
  ((Modules.EnabledResetRegister.cycleContract .bit false).evaluate
    (enabledBitInputs value enable reset) (bitState stored)).2 .stored

-- Reset wins even when enable and the ordinary input request another value.
#guard !(enabledBitNext true true true true)
-- Without reset, enable loads and disable retains.
#guard !(enabledBitNext false true false true)
#guard enabledBitNext false false false true

abbrev vectorType : SignalType := .vector 3 .bit

def vectorReset : vectorType.Denote
  | 0 => false
  | 1 => true
  | 2 => false

def vectorInput : vectorType.Denote
  | 0 => true
  | 1 => false
  | 2 => true

def resetVectorInputs (reset : Bool) :
    (Modules.ResetRegister.ports vectorType).inputs.Values
  | .value => vectorInput
  | .reset => reset

def vectorState : (Modules.Register.stateMap vectorType).Values
  | .stored => fun _ => true

def resetVectorNext (reset : Bool) :=
  ((Modules.ResetRegister.cycleContract vectorType vectorReset).evaluate
    (resetVectorInputs reset) vectorState).2 .stored

#guard !(resetVectorNext true 0)
#guard resetVectorNext true 1
#guard resetVectorNext false 0
#guard !(resetVectorNext false 1)

abbrev tupleFields : SignalTypes :=
  .ofList [.bit, .vector 2 .bit]

abbrev tupleType : SignalType := .tuple tupleFields

def tupleNaming : SignalTypeNaming tupleType :=
  .tuple (.cons "flag" .bit (.cons "payload" (.vector .bit) .nil))

def tupleReset : tupleType.Denote :=
  (false, (fun | 0 => true | 1 => false, ()))

def tupleInput : tupleType.Denote :=
  (true, (fun | 0 => false | 1 => true, ()))

def enabledTupleInputs :
    (Modules.EnabledResetRegister.ports tupleType).inputs.Values
  | .value => tupleInput
  | .enable => false
  | .reset => true

def tupleState : (Modules.Register.stateMap tupleType).Values
  | .stored => tupleInput

example :
    ((Modules.EnabledResetRegister.cycleContract tupleType tupleReset).evaluate
      enabledTupleInputs tupleState).2 .stored = tupleReset := by
  have allowed :=
    ((Modules.EnabledResetRegister.cycleContract tupleType tupleReset).evaluateStep_allowed
      enabledTupleInputs tupleState)
  exact Modules.EnabledResetRegister.next_stored_of_reset allowed rfl

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.ResetRegister.ports .bit) :=
  Modules.ResetRegister.certified .bit false

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.ResetRegister.ports vectorType) :=
  Modules.ResetRegister.certified vectorType vectorReset

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.ResetRegister.ports tupleType) :=
  Modules.ResetRegister.certified tupleType tupleReset

noncomputable example :
    Contracts.Cycle.ModuleCycleCertified (Modules.EnabledResetRegister.ports .bit) :=
  Modules.EnabledResetRegister.certified .bit false

noncomputable example :
    Contracts.Cycle.ModuleCycleCertified (Modules.EnabledResetRegister.ports vectorType) :=
  Modules.EnabledResetRegister.certified vectorType vectorReset

noncomputable example :
    Contracts.Cycle.ModuleCycleCertified (Modules.EnabledResetRegister.ports tupleType) :=
  Modules.EnabledResetRegister.certified tupleType tupleReset

example : Contracts.Cycle.Implements
    (Modules.EnabledResetRegister.moduleStructure .bit false)
    (Modules.EnabledResetRegister.cycleContract .bit false)
    (Modules.EnabledResetRegister.certification .bit false).stateCorresponds :=
  Modules.EnabledResetRegister.implements_contract .bit false

/-! The reader-facing feedback description is checked against the production
structure used by certification and FIRRTL emission. -/

example :
    (Modules.ResetRegister.description .bit false).ImplementsCycleContract
      (Modules.ResetRegister.cycleContract .bit false)
      (Modules.ResetRegister.Naming.ports .bit) :=
  Modules.ResetRegister.construction_correct .bit false

example :
    (Modules.EnabledResetRegister.description .bit false).children.map
      (fun child => child.name) =
        [SourceName.indexed "mux" 0, SourceName.indexed "reset_register" 0] := by
  rfl

example :
    (Modules.EnabledResetRegister.description .bit false).ImplementsCycleContract
      (Modules.EnabledResetRegister.cycleContract .bit false)
      (Modules.EnabledResetRegister.Naming.ports .bit) :=
  Modules.EnabledResetRegister.construction_correct .bit false

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def renders {ports : ModulePorts} {moduleStructure : ModuleStructure ports}
    (naming : ModuleNaming moduleStructure)
    (fragments : List String) : Bool :=
  match renderCircuit naming with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard renders (Modules.ResetRegister.naming .bit false)
  ["public module ResetRegister_bit_0",
   "input reset : UInt<1>",
   "inst constant_0 of constant_bit_0",
   "inst mux_0 of Mux_bit",
   "inst register_0 of register_bit"]

#guard renders (Modules.EnabledResetRegister.naming .bit false)
  ["public module EnabledResetRegister_bit_0",
   "input enable : UInt<1>",
   "input reset : UInt<1>",
   "inst reset_register_0 of ResetRegister_bit_0"]

#guard renders
  (Modules.EnabledResetRegister.namingWith tupleType tupleReset tupleNaming)
  ["input value : { flag : UInt<1>, payload : UInt<1>[2] }",
   "output value_out : { flag : UInt<1>, payload : UInt<1>[2] }",
   "inst reset_register_0 of ResetRegister"]


end SileanTests.ResetRegister
