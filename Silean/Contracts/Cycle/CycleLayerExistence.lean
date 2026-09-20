import Silean.Contracts.Cycle.CycleLayerSemantics
import Silean.Semantics.StructuralRuleExistence

namespace Silean.Contracts.Cycle.Certification.Layer

open Silean

/-! # Structural certification from cycle-layer schedules

The construction is entirely contract-independent after cycle contracts have
been viewed as structural-rule interfaces. -/

namespace RuleSchedules

/-- Parent output and state schedules that cover every child rule provide a
complete contract-independent structural certification of the composite. -/
theorem structuralCertification
    (schedules : RuleSchedules body childContracts contract)
    (covers : schedules.CoversChildren)
    (children : ChildStructures body childContracts) :
    ModuleStructuralCertification (moduleStructure body children) :=
  ModuleStructuralCertification.Layer.Schedule.certification
    schedules.combined.schedule (structuralChildren children)
    (fun _ => trivial) (schedules.combinedCovers covers)

end RuleSchedules

end Silean.Contracts.Cycle.Certification.Layer
