import Silean.Authoring.ModulePorts
import Silean.Authoring.ModuleInstances
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleWiring
import Silean.Authoring.ModuleDesign
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.SignalSchema
import Silean.Authoring.SignalSchemaDeclaration
import Silean.Authoring.CircuitArithmetic

/-! # Hardware authoring commands

The `Authoring` layer provides command syntax for declaring Silean hardware in
a readable form. These commands run during elaboration and generate ordinary
definitions from the `Foundation`, `Structure`, `Naming`, and `Contracts`
layers; they do not introduce a separate hardware representation or semantics.

A typical composite module is authored in three stages:

1. `module_design` declares its ports, child instances, wiring, and emission
   naming. The lower-level `module_ports`, `module_instances`, and
   `module_wiring` commands are also available when those pieces need to be
   declared separately.
2. `module_cycle_contract` declares the module's intended one-cycle behavior,
   independently of its structure.
3. `module_child_certifications`, `module_rule_schedules`, and
   `module_cycle_certification` connect certified children to the design and
   prove that the resulting structure implements the contract.

`signal_schema` is an optional companion for giving stable hierarchical names
to the components of aggregate signal types.
-/
