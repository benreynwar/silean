# Silean source map

This document describes current source ownership. `Architecture.md` explains
the concepts and proof boundary; `../Roadmap.md` records remaining work.

## Public aggregates

| Import | Contents |
| --- | --- |
| `Silean` | Complete library: foundation, semantics, contracts, modules, naming, and FIRRTL |
| `Silean.Foundation` | Foundational signal, label, port, and state-shape vocabulary |
| `Silean.Structure` | Child port collections, endpoints, wiring, bodies, and recursive structures |
| `Silean.Interfaces` | Reusable port groups with small boundary-level behavioral interpretations |
| `Silean.Primitives` | All supported single-bit primitive leaves and contracts |
| `Silean.Semantics` | Contract-independent structural equations, dependencies, and execution |
| `Silean.Contracts` | Cycle, reset, and FIFO contracts together with their proof machinery |
| `Silean.Composition` | Generic certified tools that construct modules from other modules |
| `Silean.Modules` | Concrete reusable hardware module designs and their public results |
| `Silean.Naming` | Generic naming metadata plus primitive, adapter, and reusable composition naming |
| `Silean.FIRRTL` | Generic traversal, rendering, validation, and emission |

Internal files import the narrow dependency they need. The aggregates are
entry points for consumers and do not create compatibility namespaces.

Directories and namespaces use the same ownership boundaries: contracts are
under `Silean.Contracts`, generic module constructors under
`Silean.Composition`, interfaces under `Silean.Interfaces`, and concrete
designs under `Silean.Modules`. Definitions that are methods of a foundational
type remain in that type's namespace even when their implementation lives in a
later layer; for example, structural semantics defines
`ModuleStructure.IsSolution`, not `Semantics.ModuleStructure.IsSolution`.
Filenames are globally distinctive so editor tabs, searches, and diagnostics
identify a source without requiring its full path.

## Foundation and structure

| Source | Responsibility |
| --- | --- |
| `Foundation/SignalType.lean` | Bit, vector, and tuple shapes and their Lean values |
| `Foundation/Enumeration.lean` | Stable finite identity enumeration and dependent maps |
| `Foundation/SignalMap.lean` | Symbolically labelled typed signal collections and values |
| `Foundation/SignalExpectation.lean` | Recursive zero/one/don't-care expectations and matching for signal values and labelled maps |
| `Foundation/SignalSelection.lean` | Typed ordered subsets of signal maps |
| `Foundation/ModulePorts.lean` | Connectivity-only input and output maps |
| `Foundation/StructuralState.lean` | Primitive-local and recursively labelled state shapes |
| `Foundation/BitVector.lean` | LSB-first finite bit-vector arithmetic and indexing laws |
| `Foundation/CircularBuffer.lean` | Generic modular distance, indexed traversal, and functional-write laws |
| `Foundation/Execution.lean` | Contract-independent deterministic runs and relational finite traces |
| `Foundation/DeriveEnumeration.lean` | Derivation support for finite symbolic label enumerations |
| `Structure/Primitive.lean` | Open primitive leaf descriptions, equations, state, and dependencies |
| `Structure/ModuleBody.lean` | One uninstantiated structural layer: child boundaries, typed endpoints, and total wiring |
| `Structure/ModuleStructure.lean` | Primitive, adapter, explicit blackbox, and recursively owned composite hierarchy; recursive closure check |

## Interfaces

| Source | Responsibility |
| --- | --- |
| `Interfaces/ValidReady.lean` | Direction-correct valid/ready sink and source selections, shared cycle samples, and finite transferred-payload extraction |
| `Interfaces/FifoPorts.lean` | Canonical FIFO boundary labels and its valid/ready sink and source selections |

An interface selects and interprets part of a module boundary. The valid/ready
interfaces say when a payload transfer occurs, but do not specify FIFO
ordering, capacity, latency, or reset behavior.

`Composition/SignalLayout.lean` and `Composition/SignalAdapter.lean` are the
deliberate low-level Composition dependency of `ModuleStructure`: they describe
closed, lossless immediate-component structural leaves.
`Composition/SignalAdapterImplementation.lean` owns their equations, cycle
contracts, and certificates; `Composition/SignalLogic.lean` contains generic
signal-value logic laws, including recursive value equality and its
equivalence to Lean equality.

## Meaning and certification

| Source | Responsibility |
| --- | --- |
| `Semantics/StructuralEquations.lean` | `ProposedValues`, order-independent structural solutions, and generic assembly of a composite solution from consistent child solutions |
| `Semantics/StructuralDependency.lean` | Semantic dependency rules and at-most-one solutions |
| `Semantics/StructuralExecution.lean` | Contract-independent one-cycle transitions and finite relational executions |
| `Contracts/Cycle/CycleContract.lean` | Rule-local output behavior and explicit-input state transitions |
| `Contracts/Cycle/CycleEvaluation.lean` | Deterministic cycle-contract application and relational laws |
| `Contracts/Cycle/CycleImplementation.lean` | State correspondence, refinement, certified structures, and parametric certified layers |
| `Contracts/Cycle/CycleLayerSchedule.lean` | The single child-implementation-independent schedule representation over a module body and its child contracts |
| `Contracts/Cycle/CycleLayerSemantics.lean` | Generic replay and structural-uniqueness proofs over contract-only layer schedules |
| `Contracts/Cycle/CycleLayerExistence.lean` | Private proof evaluator and generic structural-existence proof over the same schedules |
| `Contracts/Cycle/CycleLayerConstruction.lean` | Public child-contract helpers and generic scheduled-layer certification assembly |
| `Contracts/Reset/ResetContract.lean` | Contract-only synchronous-reset synchronization and ternary finite-trace behavior |
| `Contracts/Reset/ResetImplementation.lean` | Non-vacuous structural totality and direct structural-trace refinement for reset contracts, without a public state mapping |
| `Contracts/Fifo/FifoContract.lean` | Interface-based, latency-independent reset-synchronized FIFO traces, reusable queue laws, and non-vacuous certified bundles |
| `Contracts/Fifo/FifoPortContract.lean` | Standard FIFO contract specialized to the canonical FIFO interface |
| `Contracts/Fifo/FifoCycleBehavior.lean` | Exact ready/valid cycle behavior and its serial behavioral composition |
| `Contracts/Fifo/FifoCycleRefinement.lean` | Private-proof adapter from exact cycle certification and a logical queue invariant to FIFO certification |
| `Composition/LeafwiseComposition.lean` | Generic split/component/combine hierarchy, proposal construction, and shared component scheduling |
| `Composition/BinaryLeafwise.lean` | Certified recursive construction for stateless binary leafwise operations |
| `Composition/Reduction.lean` | Generic balanced reduction hierarchy parameterized by a binary operation and identity |
| `Composition/FifoSerialComposition.lean` | Two-child serial FIFO structure and exact cycle certification |
| `Composition/FifoSerialRefinement.lean` | Preservation of latency-independent FIFO behavior under serial composition |

Schedules are proof data. They neither belong to `ModuleStructure` nor define
its meaning.

The exact shared pattern and the boundary between generic hierarchy mechanics
and module semantics are reviewed in `LeafwiseComposition.md`.

## Hardware and behavior

`Primitives/` contains one file per supported single-bit primitive. Generic
module-building mechanisms live in `Composition/`; `Modules/` contains concrete
reusable structures, certification, public behavioral theorems, and each
module's naming metadata. `Constant` uses the generic
leafwise component/combiner hierarchy with empty input families and
value-dependent recursive leaves. `Composition.Reduction` owns generic balanced
finite reduction construction and proof machinery; `All` instantiates it with AND and
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
values once and gives every indexed combinational read port its own
`CombMuxTree`; its contract
uses an ordinary vector state and functional replacement rather than exposing
the hierarchy. Register-bank child identities are a private named inductive;
their executable enumeration lists those constructors directly. A public
closure theorem composes reusable closure laws from the generic leafwise
hierarchy and child modules, so clients need not unfold those identities.
Decoder,
mux-tree, and register-bank contracts share `BitVector.toIndex` from the
foundation arithmetic utilities. The XOR primitive and `HalfAdder` provide the
first arithmetic layer used by the ripple incrementer. HalfAdder owns two
independent output rules and composes XOR/AND structurally; its public
arithmetic law depends only on its contract results. `FullAdder` adds the
three-input layer with two HalfAdders and an OR gate while exposing only its
direct Boolean and numeric contract. `Add` recursively composes FullAdders for
two arbitrary LSB-first vectors and exposes the complete result-plus-carry
numeric identity. `BitwiseXor` adds generic leafwise XOR for arbitrary signal
shapes. `AddSub` combines it with Add behind an independent direct
carry/borrow contract and exposes modular arithmetic plus no-borrow laws.
`Increment` builds the next arithmetic
layer: its public behavior is addition of one modulo the vector
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
`FifoProperties` gives this cycle contract its logical queue interpretation and
proves the reachable occupancy invariant, empty/full boundaries, and exact
ordinary-cycle enqueue/dequeue behavior. Generic circular-buffer arithmetic
lives in `Foundation/CircularBuffer.lean`. `Contracts.Fifo.FifoCertified` uses those facts to
prove the pointer structure satisfies the shared `Contracts/Fifo/FifoContract.lean`
boundary contract; it does not inspect structural children.
The serial FIFO family uses `Interfaces.Fifo`, the shared resettable boundary.
`Contracts.Fifo.Cycle` turns ready/valid/reset functions into cycle contracts
and composes their behavior serially. `Composition.FifoSerial` constructs and
certifies a two-child serial hierarchy using only child public contracts and
refinements. `SerialDepthFifo` is the concrete recursive positive-depth module
that applies those generic composition laws. Structural module files do not own
trace execution machinery.

## Naming and backend

`Naming/` owns generic executable naming metadata in `Silean.Naming`, including
the shared FIFO boundary naming used by every FIFO implementation and the
generic binary-leafwise, reduction-tree, and serial-FIFO hierarchy traversals.
Module-specific metadata is in `Silean.Modules.<Module>.Naming`, inside the
module's source file. `FIRRTL/` owns only backend operations in
`Silean.FIRRTL`: hierarchy traversal, identifier and definition validation,
FIRRTL 4 text rendering, and the shared emitter command-line shell.

Configured top-level designs live in `Emitters/`. They select an ordinary Lean
module structure and naming value and call either the blackbox-capable renderer
or the closed renderer with a `HasNoBlackboxes` proof. They contain no alternate
circuit representation.

## Regression ownership

- `Examples/Fixtures/` contains test-only designs and shared check inputs used
  by multiple regressions. Nothing in the reusable library imports this
  directory.
- `Examples/Checks/` contains Lean compile-time and executable checks.
- `SileanExamples.lean` is the aggregate regression target.
- `tests/` contains cocotb tests and per-design simulator configuration,
  including randomized ready/valid scoreboard coverage for the configured
  generic FIFO built from a register bank with read and write pointers.
- `Makefile` runs Lean emission, CIRCT `firtool`, Verilator, and cocotb.
- `build/` contains generated FIRRTL, SystemVerilog, and simulator artifacts;
  it is never a semantic or proof input.
