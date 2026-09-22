import Silean.Semantics.FixedLatency

namespace SileanTests.FixedLatencyChecks

open Silean

example
    (left : FixedLatency.Relates leftLatency leftRelation inputs intermediate)
    (right : FixedLatency.Relates rightLatency rightRelation intermediate outputs) :
    FixedLatency.Relates (leftLatency + rightLatency)
      (FixedLatency.Comp leftRelation rightRelation) inputs outputs :=
  FixedLatency.serial left right

example
    (left : FixedLatency.Relates latency leftRelation inputs outputs)
    (right : FixedLatency.Relates latency rightRelation inputs outputs) :
    FixedLatency.Relates latency
      (fun input output =>
        leftRelation input output ∧ rightRelation input output)
      inputs outputs :=
  FixedLatency.and left right

example
    (left : FixedLatency.Computes leftLatency leftFunction inputs intermediate)
    (right : FixedLatency.Computes rightLatency rightFunction intermediate outputs) :
    FixedLatency.Computes (leftLatency + rightLatency)
      (rightFunction ∘ leftFunction) inputs outputs :=
  FixedLatency.computes_serial left right

example
    (left : FixedLatency.Computes latency leftFunction inputs leftOutputs)
    (right : FixedLatency.Computes latency rightFunction inputs rightOutputs) :
    FixedLatency.Computes latency
      (fun input => (leftFunction input, rightFunction input)) inputs
      (leftOutputs.zip rightOutputs) :=
  FixedLatency.computes_parallel left right

end SileanTests.FixedLatencyChecks
