# Silean 2 source map

This document describes current source ownership. `Architecture.md` explains
the concepts and proof boundary; `../Roadmap.md` records remaining work.

## Public aggregates

| Import | Contents |
| --- | --- |
| `Silean2` | Complete library: foundation, semantics, contracts, modules, naming, and FIRRTL |
| `Silean2.Foundation` | Foundational signal, label, port, and state-shape vocabulary |
| `Silean2.Structure` | Instances, endpoints, wiring, bodies, and recursive structures |
| `Silean2.Primitives` | All supported single-bit primitive leaves and contracts |
| `Silean2.Contracts` | Implementation-independent no-reset FIFO contracts and execution |
| `Silean2.Modules` | Reusable certified hardware modules and FIFO behavior/results |
| `Silean2.Naming` | Generic naming metadata plus primitive and adapter naming |
| `Silean2.FIRRTL` | Generic traversal, rendering, validation, and emission |

Internal files import the narrow dependency they need. The aggregates are
entry points for consumers and do not create compatibility namespaces.

## Foundation and structure

| Source | Responsibility |
| --- | --- |
| `Foundation/SignalType.lean` | Bit, vector, and tuple shapes and their Lean values |
| `Foundation/Enumeration.lean` | Stable finite identity enumeration and dependent maps |
| `Foundation/SignalMap.lean` | Symbolically labelled typed signal collections and values |
| `Foundation/SignalSelection.lean` | Typed ordered subsets of signal maps |
| `Foundation/ModulePorts.lean` | Connectivity-only input and output maps |
| `Foundation/StructuralState.lean` | Primitive-local and recursively labelled state shapes |
| `Structure/Instances.lean` | Canonically ordered child names and exact child ports |
| `Structure/Endpoint.lean` | Typed module/instance signal sources and sinks |
| `Structure/Wiring.lean` | Total same-type driver functions for every sink |
| `Structure/ModuleBody.lean` | One boundary, child collection, and complete wiring |
| `Structure/ModuleStructure.lean` | Primitive, adapter, and recursively owned composite hierarchy |

`SignalLayout.lean` and `SignalAdapter.lean` describe immediate aggregate
components. `SignalAdapterCertified.lean` proves splitter and combiner
certificates; `SignalLogic.lean` contains generic signal-value logic laws.

## Meaning and certification

| Source | Responsibility |
| --- | --- |
| `StructuralSemantics.lean` | `ProposedValues` and order-independent structural solutions |
| `StructuralDependency.lean` | Semantic dependency rules and at-most-one solutions |
| `ModuleCycleContract.lean` | Rule-local output behavior and explicit-input state transitions |
| `ModuleCycleEvaluation.lean` | Deterministic contract application and its relational laws |
| `ModuleCycleCertified.lean` | State correspondence, refinement, existence, and uniqueness package |
| `CertifiedComposition.lean` | Typed certified child collections and child refinement laws |
| `CertifiedSchedule.lean` | Parent-owned output/state availability schedules and coverage |
| `LeafwiseComposition.lean` | Generic split/component/combine hierarchy, proposal construction, and shared component scheduling |

Schedules are proof data. They neither belong to `ModuleStructure` nor define
its meaning.

The exact shared pattern and the boundary between generic hierarchy mechanics
and module semantics are reviewed in `LeafwiseComposition.md`.

## Hardware and behavior

`Primitives/` contains one file per supported single-bit primitive. `Modules/`
contains reusable structures, contracts, certification, public behavioral
theorems, and each module's naming metadata. FIFO responsibilities are split
explicitly: `FifoInterface` owns the shared ports and rules,
`FifoCycleBehavior` turns ready/valid functions into cycle contracts and
composes them, `FifoExecution` interprets those contracts over finite input
sequences, and `*Properties` proves conservation, capacity, and ready
propagation. Structural module files do not own execution machinery.

`Contracts/NoResetFifo*.lean` contains implementation-independent FIFO trace,
serial-composition, execution, and view laws. It does not inspect structural
hierarchy.

## Naming and backend

`Naming/` owns generic executable naming metadata in `Silean2.Naming`.
Module-specific metadata is in `Silean2.Modules.<Module>.Naming`, inside the
module's source file. `FIRRTL/` owns only backend operations in
`Silean2.FIRRTL`: hierarchy traversal, identifier and definition validation,
FIRRTL 4 text rendering, and the shared emitter command-line shell.

Configured top-level designs live in `Emitters/`. They select an ordinary Lean
module structure and naming value, call the generic renderer, and contain no
proof or alternate circuit representation.

## Regression ownership

- `Examples/Fixtures/` contains small test-only designs shared by multiple
  regressions. Nothing in the reusable library imports this directory.
- `Examples/Checks/` contains Lean compile-time and executable checks.
- `Silean2Examples.lean` is the aggregate regression target.
- `tests/` contains cocotb tests and per-design simulator configuration.
- `Makefile` runs Lean emission, CIRCT `firtool`, Verilator, and cocotb.
- `build/` contains generated FIRRTL, SystemVerilog, and simulator artifacts;
  it is never a semantic or proof input.
