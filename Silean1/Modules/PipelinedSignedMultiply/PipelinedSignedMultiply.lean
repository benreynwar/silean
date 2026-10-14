import Silean.Authoring.ModulePorts
import Silean.Modules.SignedMultiply.SignedMultiply
import Silean.Semantics.FixedLatency

/-! # Pipelined full-width signed multiplication

`PipelinedSignedMultiply` has the same arithmetic behavior as
`SignedMultiply`, with a statically known latency. This file contains only its
public boundary and trace-level contract. Pipeline placement belongs to the
later hardware structure.
-/

namespace Silean.Modules.PipelinedSignedMultiply

open Silean

module_ports ports (leftWidth : Nat) (rightWidth : Nat) where
  input left : .vector leftWidth .bit,
  input right : .vector rightWidth .bit,
  output result : .vector (leftWidth + rightWidth) .bit

/-- Every input in a trace whose corresponding delayed output also occurs is
observed as the exact full-width signed product at that later position. -/
def contract (leftWidth rightWidth latency : Nat)
    (trace : BoundaryTrace (ports leftWidth rightWidth)) : Prop :=
  FixedLatency.Holds latency
    (fun (input : (ports leftWidth rightWidth).inputs.Values)
        (output : (ports leftWidth rightWidth).outputs.Values) =>
      output .result = SignedMultiply.resultValue leftWidth rightWidth
        (input .left) (input .right)) trace

end Silean.Modules.PipelinedSignedMultiply
