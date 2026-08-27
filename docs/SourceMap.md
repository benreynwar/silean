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
| `Foundation/BitVector.lean` | LSB-first finite bit-vector arithmetic and indexing laws |
| `Foundation/CircularBuffer.lean` | Generic modular distance, indexed traversal, and functional-write laws |
| `Foundation/Execution.lean` | Contract-independent deterministic steps and finite input-sequence runs |
| `Structure/Instances.lean` | Canonically ordered child names and exact child ports |
| `Structure/Endpoint.lean` | Typed module/instance signal sources and sinks |
| `Structure/Wiring.lean` | Total same-type driver functions for every sink |
| `Structure/ModuleBody.lean` | One boundary, child collection, and complete wiring |
| `Structure/ModuleStructure.lean` | Primitive, adapter, and recursively owned composite hierarchy |

`SignalLayout.lean` and `SignalAdapter.lean` describe immediate aggregate
components. `SignalAdapterCertified.lean` proves splitter and combiner
certificates; `SignalLogic.lean` contains generic signal-value logic laws,
including recursive value equality and its equivalence to Lean equality.

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
theorems, and each module's naming metadata. `Constant` uses the generic
leafwise component/combiner hierarchy with empty input families and
value-dependent recursive leaves. `Reduction` owns generic balanced finite
reduction construction and proof machinery; `All` instantiates it with AND and
true while exposing a separate, natural every-input contract. `Equality`
recursively splits aggregates, compares corresponding children, and reduces
their result-bit family through `All`, while its contract exposes only natural
value equality. `VectorConcat` splits two vectors of a common element type and
combines their elements in left-then-right order, while exposing only natural
index laws and keeping aggregate elements intact. `BinaryToOneHot` interprets
LSB-first input bits numerically and implements the one-hot result through a
recursive decoder, two masks, and `VectorConcat`. `VectorSplit` partitions a
vector through existing generic adapters. `CombMuxTree` recursively applies
that partition, two smaller trees, and `Mux` while exposing direct numeric
selection as its contract. `RegisterBank` uses `BinaryToOneHot` and a family of
generic enabled registers for synchronous writes, then combines their current
values and selects a combinational read through `CombMuxTree`; its contract
uses an ordinary vector state and functional replacement rather than exposing
the hierarchy. Register-bank child identities are a private named inductive;
their executable enumeration lists those constructors directly. Decoder,
mux-tree, and register-bank contracts share `BitVector.toIndex` from the
foundation arithmetic utilities. The XOR primitive and `HalfAdder` provide the
first arithmetic layer used by the ripple incrementer. HalfAdder owns two
independent output rules and composes XOR/AND structurally; its public
arithmetic law depends only on its contract results. `Increment` builds the
next arithmetic layer: its public behavior is addition of one modulo the vector
cardinality, while its private recursive helper carries from lower indices into
one HalfAdder at each successive high index. `ResetRegister` composes Constant,
Mux, and Register for synchronous configured reset; `EnabledResetRegister`
wraps that certified storage with enable/hold selection and gives reset highest
priority. Neither requires reset-aware primitives. `FifoPointerControl` owns
the natural contract and certified combinational structure for interpreting
address-plus-wrap pointers. Direct splitters expose address and wrap bits, one
generic address Equality and one primitive wrap equality distinguish empty
from full, and ordinary gates derive valid/ready transfer enables. It has no
state or reset input. `EnabledResetCounter` composes Increment and
EnabledResetRegister into the generic synchronous state element used by FIFO
pointers; its public
contract describes modular arithmetic rather than feedback wiring.
`Fifo` is the certified pointer-and-register-bank composition: two
zero-reset counters feed FifoPointerControl, whose addresses and transfer
enables drive RegisterBank and the counters. Its contract owns logical pointer
and entry state and remains independent of those four structural children.
Reset is synchronous: it wins in pointer next state without suppressing the
current pre-edge handshake or clearing storage.
`FifoProperties` gives this contract its logical queue interpretation and
proves the reachable occupancy invariant, empty/full boundaries, exact
enqueue/dequeue behavior, reset clearing, and arbitrary finite-trace FIFO
ordering. Generic circular-buffer arithmetic lives in
`Foundation/CircularBuffer.lean`; the small contract-independent finite runner
lives in `Foundation/Execution.lean`; reset-aware queue observations,
transitions, and trace lifting live in `Contracts/ResetFifo.lean`. The property
proof consumes the public `Fifo` contract evaluator and does not inspect
structural children.
The separate no-reset serial family is explicit:
`NoResetFifoInterface` owns its shared ports and rules,
`NoResetFifoCycleBehavior` turns ready/valid functions into cycle contracts,
`NoResetFifoExecution` interprets those contracts over finite input sequences,
and `SerialDepthFifo` owns the recursive positive-depth implementation and its
properties. Structural module files do not own execution machinery.

`Contracts/NoResetFifo*.lean` contains implementation-independent no-reset FIFO
trace, serial-composition, execution, and view laws. `Contracts/ResetFifo.lean`
contains reset-aware queue steps and finite transition lifting. Neither layer
inspects structural hierarchy.

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
