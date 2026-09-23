# Silean source map

This document answers where a Silean concept lives. For why the layers are
separate, see [Architecture.md](Architecture.md). For conventions when adding a
module, see [ModuleOrganization.md](ModuleOrganization.md). Current project
work belongs in the [roadmap](../../Roadmap.md), not here.

## Public entry points

| Import | Purpose |
| --- | --- |
| `Silean` | Complete public library |
| `Silean.Foundation` | Signal shapes, labels, values, ports, and state shapes |
| `Silean.Structure` | Primitives, module bodies, and concrete recursive structures |
| `Silean.Semantics` | Contract-independent equations, execution, traces, and structural certification |
| `Silean.Contracts` | Reusable behavioral contract forms and their certification machinery |
| `Silean.Interfaces` | Reusable interpretations of groups of boundary ports |
| `Silean.Composition` | Generic module constructions parameterized by children or operations |
| `Silean.Primitives` | Supported primitive leaves and their public behavior |
| `Silean.Modules` | Concrete reusable hardware modules |
| `Silean.Authoring` | Commands and helpers that generate ordinary Silean definitions |
| `Silean.Naming` | Emission naming metadata |
| `Silean.FIRRTL` | FIRRTL traversal, validation, rendering, and emission |

Library sources should import the narrowest layer they need. Applications may
use `import Silean` when the complete API is more convenient.

## Foundation and structure

`Silean/Foundation/` owns the typed vocabulary used by every later layer.

| Source | Responsibility |
| --- | --- |
| `SignalType.lean` | Bit, vector, and tuple shapes and their Lean denotations |
| `Enumeration.lean`, `DeriveEnumeration.lean` | Stable finite symbolic identities |
| `SignalMap.lean` | Labelled dependently typed collections of signals and values |
| `SignalSelection.lean`, `SignalGroup.lean` | Typed subsets and label-preserving views |
| `SignalLayout.lean` | Packing, unpacking, positions, and aggregate field access |
| `ModulePorts.lean` | Typed input and output boundaries |
| `BoundaryStep.lean`, `CycleStep.lean` | Shared boundary and stateful step records |
| `StructuralState.lean` | Primitive-local and recursively labelled state shapes |
| `BitVector.lean` | LSB-first finite Boolean-vector arithmetic and laws |

`Silean/Structure/` owns hardware syntax, without behavioral contracts or an
evaluation order.

| Source | Responsibility |
| --- | --- |
| `Primitive.lean` | Primitive ports, state, equations, and dependencies |
| `ModuleBody.lean` | One hierarchy layer: parent boundary, child boundaries, and total typed wiring |
| `ModuleStructure.lean` | Concrete primitive, adapter, and recursively composite structures |

## Structural meaning and time

`Silean/Semantics/` gives structures their mathematical meaning independently
of any particular contract.

| Source | Responsibility |
| --- | --- |
| `StructuralEquations.lean` | `HierStep` and simultaneous structural solutions |
| `StructuralDependency.lean` | Boundary dependency rules, uniqueness, and structural certification |
| `StructuralRuleSemantics.lean` | Semantic composition of child dependency rules |
| `StructuralRuleSchedule.lean` | Checked schedules over child structural rules |
| `StructuralRuleDerivation.lean` | Deriving usable parent rules from schedules |
| `StructuralRuleExistence.lean` | Constructing solutions from complete schedules |
| `StructuralExecution.lean` | Transitions and finite execution of concrete hierarchies |
| `StructuralObservation.lean` | Boundary observation, child projections, and concrete-to-body-trace bridges |
| `Trace.lean` | Generic finite relational traces and composition laws |
| `BoundaryTrace.lean` | State-free sequences of boundary observations |
| `ModuleBodyTrace.lean` | Synchronized parent and immediate-child traces for a `ModuleBody` |
| `DelayLine.lean` | Pure finite delay-line semantics used by temporal proofs |
| `FixedLatency.lean` | Pointwise fixed-latency trace relations and composition |
| `FramedLatency.lean` | Marker-delimited fixed-size frame relations and composition |

The important boundary is that schedules prove existence and uniqueness; they
do not define the meaning of a structure.

## Behavioral contracts

`Silean/Contracts/` contains reusable specification styles. A module may also
use an ordinary project-specific predicate when none of these is the natural
interface.

| Area | Responsibility |
| --- | --- |
| `Cycle/CycleContract.lean` | Named exact output rules and next-state behavior |
| `Cycle/CycleEvaluation.lean` | Deterministic evaluation and relational laws for cycle contracts |
| `Cycle/CycleImplementation.lean` | State correspondence and concrete certification |
| `Cycle/CycleTrace.lean` | Trace consequences of cycle certification |
| `Cycle/CycleLayerSchedule.lean` | Contract-level schedules over immediate children |
| `Cycle/CycleLayerSemantics.lean` | Generic replay and uniqueness for those schedules |
| `Cycle/CycleLayerExistence.lean` | Generic structural existence for those schedules |
| `Cycle/CycleLayerConstruction.lean` | Public child-contract matches and certification assembly |
| `Cycle/CycleScheduleDerivation.lean` | Derived cycle schedule support |
| `Reset/` | Reset-synchronized trace contracts and implementations |
| `Fifo/` | Exact and latency-independent FIFO behavior and refinement |
| `SignalExpectation.lean` | Recursive zero, one, and don't-care expectations |

`Silean/Interfaces/` is deliberately weaker than a behavioral contract. For
example, `ValidReady.lean` identifies transfers on a group of ports, while
`FifoPorts.lean` supplies the canonical FIFO boundary; neither alone specifies
queue ordering or capacity.

## Authoring

`Silean/Authoring/` removes repeated typed boilerplate. Its commands elaborate
to definitions in the foundation, structure, naming, and contract layers; it
does not introduce another semantics.

| Source | Responsibility |
| --- | --- |
| `SignalSchemaDeclaration.lean` | `signal_schema` declarations for reusable aggregate shapes, labels, accessors, and naming |
| `ModulePorts.lean` | `module_ports` declarations and generated typed boundary helpers |
| `ModuleInstances.lean`, `ModuleWiring.lean` | Lower-level child-family and wiring declarations |
| `ModuleDesign.lean` | `module_design`, including concrete and unresolved immediate children |
| `ModuleCycleContract.lean` | `module_cycle_contract` and generated public rule equations |
| `ModuleChildCertifications.lean` | Association of concrete children with their public certifications |
| `ModuleRuleSchedules.lean` | `module_rule_schedules` and contract-independent `module_complete_schedule` |
| `ModuleCycleCertification.lean` | Final assembly of exact cycle certification |

`CircuitDescription.lean` and its logic, arithmetic, selection, contract, and
soundness companions provide an optional human-oriented builder notation used
by some existing modules. A circuit description is not the production
structure: when one is retained, a correspondence proof connects it to the
`ModuleStructure`. New modules should not add this second presentation unless
it materially improves readability.

`SignalSchema.lean` is the small authoring-facing alias for aggregate naming
metadata, and `FifoPorts.lean` supplies builder adapters for the shared FIFO
interface.

## Composition, primitives, and modules

`Silean/Composition/` owns constructions that are generic in a signal shape,
operation, or certified child:

- lossless aggregate splitters and combiners;
- recursive signal logic;
- leafwise unary and binary construction;
- balanced reduction; and
- serial FIFO composition and refinement.

`Silean/Primitives/` owns supported primitive leaves. Files ending in
`Primitive.lean` define their structural equations; the corresponding short
module files expose their public behavior and designs.

`Silean/Modules/` owns concrete reusable hardware. Each nontrivial module has a
small public definition file, an optional `Derived` facade, and implementation
and proof details under its own `Internal/` directory. The exact convention is
described in [ModuleOrganization.md](ModuleOrganization.md).

Client-specific hardware stays with its client. In particular, fixed-point FFT
policy and streaming FFT modules belong under `HTFFT/`, while PicoRV-specific
hardware belongs under `PicoRV/`. A useful component moves into
`Silean/Modules/` only when its interface is genuinely reusable.

## Naming and emission

`Silean/Naming/ModuleNaming.lean` defines recursive emission metadata.
Specialized files provide naming for primitives, signal adapters, generic
leafwise structures, reductions, and FIFO composition.

`Silean/FIRRTL/` owns the backend:

| Source | Responsibility |
| --- | --- |
| `Traversal.lean` | Recursive collection of definitions from a named structure |
| `Render.lean` | Validation and FIRRTL 4 text generation |
| `Emit.lean` | Shared command-line emission support |

Configured library entry points live in `Silean/Emitters/`. Generated FIRRTL,
SystemVerilog, and simulator output under `build/` are regression artifacts and
never proof inputs.

## Tests

- `tests/silean/lean/SileanTests/` contains Lean-facing library regressions.
- `tests/htfft/` and `tests/picorv/` contain client regressions.
- `tests/*/Fixtures/` contains test-only designs and shared inputs; reusable
  library code must not import it.
- The top-level `Makefile` coordinates Lean emission, CIRCT lowering,
  Verilator, and cocotb where configured.

The formal boundary currently ends at `ModuleStructure`. Backend lowering and
simulation provide valuable validation, but are not inputs to Lean correctness
theorems.
