import Silean2.FIRRTL
import Silean2.Modules.Constant

namespace Silean2.Examples.Checks.Constant

open Silean2 Silean2.FIRRTL Silean2.Naming

def signalType : SignalType :=
  .tuple (.cons (.vector 2 .bit) (.cons .bit .nil))

def value : signalType.Denote :=
  (fun index => index == 0, (true, ()))

def typeNaming : SignalTypeNaming signalType :=
  .tuple (.cons "payload" (.vector .bit) (.cons "valid" .bit .nil))

noncomputable example : ModuleCycleCertified (Modules.Constant.ports signalType) :=
  Modules.Constant.certified signalType value

example (inputs : (Modules.Constant.ports signalType).inputs.Values)
    (state : (Modules.Constant.cycleContract signalType value).state.Values) :
    ((Modules.Constant.cycleContract signalType value).evaluate inputs state).1
        .output = value := by
  have holds := ((Modules.Constant.cycleContract signalType value).evaluate_evaluatesTo
    inputs state).1 Primitives.ConstantRule.apply
  exact (Modules.Constant.outputRule_holds_iff signalType value _ _ _).mp holds

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (result : RenderResult String)
    (fragments : List String) : Bool :=
  match result with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard containsAll (renderCircuit (Silean2.Naming.Primitive.constant true))
  ["public module constant_true", "connect out, UInt<1>(1)"]

#guard containsAll
    (renderCircuit (Modules.Constant.Naming.namingWith signalType value typeNaming))
  ["public module constant_structural_t_v2_bit_bit_unit_1_0_1",
   "module constant_true", "module constant_false",
   "inst constant_component_0 of constant_structural_v2_bit_1_0",
   "output value : { payload : UInt<1>[2], valid : UInt<1> }"]

end Silean2.Examples.Checks.Constant
