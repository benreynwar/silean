import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A combinational reorganization of a bit vector. Every output bit selects
one input bit or a Boolean constant. This covers permutations, duplication,
truncation, extension, and insertion of fixed bits without embedding those
layouts in bespoke wiring code. -/

namespace VectorLayout

/-- The source selected for one output bit of a vector layout. -/
inductive BitSource (inputWidth : Nat) where
  | input (index : Fin inputWidth)
  | constant (value : Bool)
deriving DecidableEq, Repr

def BitSource.IsInput : BitSource inputWidth → Prop
  | .input _ => True
  | .constant _ => False

instance (source : BitSource inputWidth) : Decidable source.IsInput :=
  match source with
  | .input _ => isTrue trivial
  | .constant _ => isFalse id

def BitSource.inputIndex (source : BitSource inputWidth)
    (_ : source.IsInput) : Fin inputWidth :=
  match source with
  | .input index => index

def apply (layout : Fin outputWidth → BitSource inputWidth)
    (input : Fin inputWidth → Bool) : Fin outputWidth → Bool :=
  fun index => match layout index with
    | .input source => input source
    | .constant value => value

private def sourceCode : BitSource inputWidth → String
  | .input index => s!"i{index.val}"
  | .constant false => "f"
  | .constant true => "t"

/-- Stable emission identity for a concrete layout. -/
def variant (layout : Fin outputWidth → BitSource inputWidth) : String :=
  String.intercalate "_" <|
    (List.finRange outputWidth).map fun index => sourceCode (layout index)

def splitter (inputWidth : Nat) : Composition.SignalSplitter :=
  .vector inputWidth .bit

def combiner (outputWidth : Nat) : Composition.SignalCombiner :=
  .vector outputWidth .bit

module_ports ports (inputWidth : Nat) (outputWidth : Nat) where
  input input : .vector inputWidth .bit,
  output output : .vector outputWidth .bit

end VectorLayout

module_design VectorLayout (inputWidth : Nat) (outputWidth : Nat)
    (layout : Fin outputWidth → VectorLayout.BitSource inputWidth)
    (variant := VectorLayout.variant layout)
    (specialization := [.natural inputWidth, .natural outputWidth]) where
  boundary (VectorLayout.ports inputWidth outputWidth)
    (naming := VectorLayout.Naming.ports inputWidth outputWidth)
  instances {
    split := Silean.Naming.SignalAdapter.splitterDesign
      (VectorLayout.splitter inputWidth),
    falseBit := Primitives.constantDesign false,
    trueBit := Primitives.constantDesign true,
    combine := Silean.Naming.SignalAdapter.combinerDesign
      (VectorLayout.combiner outputWidth) }
  wiring {
    outputs {
      .output := combine.value }
    instance (.split) {
      .value := input.input }
    instance (.falseBit) {}
    instance (.trueBit) {}
    instance (.combine) {
      index := from (if isInput : (layout index).IsInput then
          (context inputWidth outputWidth layout).instanceOutput .split
            ((layout index).inputIndex isInput)
        else if _isTrue : layout index = .constant true then
          (context inputWidth outputWidth layout).instanceOutput .trueBit .output
        else
          (context inputWidth outputWidth layout).instanceOutput .falseBit .output) }
  }

end Silean.Modules

namespace Silean.Modules.VectorLayout

open Silean
open Silean.Authoring

module_cycle_contract cycleContract (inputWidth : Nat) (outputWidth : Nat)
    (layout : Fin outputWidth → BitSource inputWidth)
    for ports inputWidth outputWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [input]
    writes := { output := VectorLayout.apply layout input }
  state_rule where
    reads := []
    next := {}

/-- Every contract-allowed layout step produces the specified bit layout. -/
theorem output_of_allowed (inputWidth outputWidth : Nat)
    (layout : Fin outputWidth → BitSource inputWidth)
    {step : (cycleContract inputWidth outputWidth layout).Step}
    (allowed : (cycleContract inputWidth outputWidth layout).Allows step) :
    step.outputs .output = VectorLayout.apply layout (step.inputs .input) :=
  (applyRule_holds_iff inputWidth outputWidth layout
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

end Silean.Modules.VectorLayout
