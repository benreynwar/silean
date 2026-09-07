# Silean codebase audit

Date: 2026-08-31

## Scope and method

This is a current-state audit of the complete repository, not a history of how
it reached that state. It covers every checked-in Lean source, the aggregate
imports, documentation, FIRRTL emitters, Makefiles, Nix environment, and
cocotb tests. Generated files and ignored editor/simulator artifacts were
inspected as repository-hygiene inputs, but are not source.

The review followed the data flow from signal shapes and structural equations,
through cycle/reset/FIFO contracts and certification, into concrete modules,
naming, FIRRTL generation, and executable tests. It also compared imports,
public declarations, repeated proof/construction patterns, file sizes, and the
three nearly identical bitwise implementations.

Validation after the 2026-09-01 cleanup:

- `lake build` completes all 183 jobs successfully;
- there are no occurrences of `sorry`, `admit`, custom `axiom`, or `unsafe` in
  the Lean sources; and
- `nix develop -c make test` passes the bit-register, structured-FIFO,
  register-bank, and pointer-FIFO generated-hardware regressions; and
- `make check-example-imports` confirms that every `*Checks.lean` file is
  imported by `SileanExamples.lean`.

## Executive conclusion

The foundation is substantially sounder than the amount of code might suggest.
I did not find a loophole that makes the main certification claims vacuous.
Structural meaning is an order-independent relation; cycle certification
separately requires existence and uniqueness; and refinement quantifies over
every structural solution. Reset and FIFO contracts also require structural
executions to exist before constraining every such execution. Explicit
blackboxes are assumptions by design and the recursive closure property keeps
that distinction visible.

The duplicate schedule/construction layer and copied bitwise implementations
identified by the audit have been replaced by one structure-first schedule
stack and generic binary leafwise composition. The architecture, roadmap, and
PicoRV planning documents have also been consolidated around the current
design.

The concrete backend/test inconsistencies found during the audit have now been
fixed. The remaining work is architectural simplification and documentation
cleanup rather than restoring a broken regression boundary.

## Correctness review

### What is solid

1. **Structural equations are the meaning.** `ProposedValues` merely proposes
   boundary, child, and next-state values. `ModuleStructure.IsSolution` checks
   all primitive, child, and wiring equations simultaneously. A schedule is a
   proof device and is not the definition of execution.

2. **Certification is non-vacuous.** `ModuleCycleCertification` requires a
   structural result for every input and structural state, at most one result,
   a corresponding contract state for every structural state, and refinement
   of every result. A contradictory structure therefore cannot pass merely
   because an implication has no satisfying premise.

3. **Abstract state is handled correctly.** The cycle-state correspondence is
   intentionally not required to be a bijection or a function. This is still
   strong enough because every related abstract state must explain the unique
   structural result and the relation must be preserved.

4. **Higher-level contracts retain existence.** Reset and FIFO certifications
   quantify over structural executions only after requiring the relevant
   solutions/executions to exist. Their absence of a structural-state mapping
   is therefore abstraction, not a vacuity hole.

5. **Blackboxes are explicit.** A blackbox's cycle certificate follows its
   assumed primitive-like equations, which is necessarily tautological. This
   is safe only because `.blackbox` remains a distinct structural constructor
   and `HasNoBlackboxes`/`hasNoBlackboxes` recursively expose whether all such
   assumptions have been discharged. The current PicoRV top-level result is a
   composition theorem conditional on its blackbox child contracts, not yet a
   closed CPU implementation.

6. **The Boolean limitation is documented.** The model does not cover X/Z,
   analogue timing, metastability, clock-domain crossings, or backend
   equivalence. FIRRTL and SystemVerilog testing is useful evidence, but is not
   part of the Lean theorem.

### Remaining assurance gaps

- There is no proved semantics-preserving connection from FIRRTL rendering to
  `ModuleStructure.IsSolution`. That is an explicit project boundary, but the
  README should continue to state it prominently.
- The source search supports the “no custom axioms” claim, but there is no
  small checked regression recording the axioms used by the principal public
  FIFO certificates. Adding a human-reviewed `#print axioms` audit target (or
  documenting the manual command) would make that claim easier to recheck.
- The renderer validates identifiers, local name collisions, rendered module
  key collisions, and two different bodies sharing one key. This is good
  defensive checking, but `ModuleKey` and naming remain trusted executable
  metadata rather than certified identities.

## Findings, in priority order

### 1. Emitted-port naming contract (resolved)

RegisterBank retains indexed public read-port names such as
`read_0_address_0`. Its FIRRTL check and cocotb test use the same spelling, so
future drift is caught both before and after Verilog generation.

### 2. Cycle certification stack (resolved)

Cycle certification now has one structure-first path:

- `CycleLayerSchedule.lean` defines contract-only output and state schedules;
- `CycleLayerSemantics.lean` proves replay and structural uniqueness;
- `CycleLayerExistence.lean` privately evaluates proof schedules to establish
  structural existence; and
- `CycleLayerConstruction.lean` exposes child-contract proof helpers.

The former `Certification.Semantics`, `Certification.Children`,
`CycleSchedule.lean`, `CycleConstruction.lean`, and their adapters have been
removed. Module proofs supply concrete certified children only when applying
the generic structural theorems.

### 3. Binary leafwise module family (resolved)

`Composition.BinaryLeafwise` now contains the single certified implementation
of the shared bit-wrapper and recursive split/component/combine hierarchy. Its
`Operation` and `BitGate` parameters capture the actual differences: natural
Lean behavior, the aggregate split law, certified bit contract, selected rule,
dependencies, and bit result law.

`BitwiseAnd.lean`, `BitwiseOr.lean`, and `BitwiseXor.lean` are thin named
instantiations with no copied schedules or recursive proofs. The shared
construction prevents their structural and certification logic from drifting.

`Mask` and `Register` use related but genuinely different leafwise interfaces
(broadcast input and state respectively); do not force them into the binary
abstraction merely to maximize reuse.

### 4. Closed emission (resolved)

Every concrete synthesis emitter uses `renderClosedCircuit`, making the
recursive no-blackbox proof a build guard. `renderCircuit` remains available
for intentional staging structures such as PicoRV.

### 5. Structured FIFO reset regression (resolved)

The structured-FIFO test drives synchronous reset before traffic and exercises
a randomized valid/ready stream followed by a forced drain. It no longer
depends on simulator initialization or leaves reset undriven.

### 6. Composition dependency direction (resolved)

Generic Composition now imports neither concrete Modules nor Naming.
Reduction already received a certified identity source as an input; the
`Modules.Constant` import was stale and also happened to provide naming
transitively. Reduction naming and serial-FIFO naming now live separately in
`Naming/ReductionNaming.lean` and `Naming/FifoSerialNaming.lean`.

`SignalAdapter` is a deliberate low-level exception within Composition.
Splitter and combiner shapes are closed, lossless structural leaf descriptions
which `ModuleStructure` must mention directly; they are not ordinary concrete
modules or programmable primitives. `SignalLayout` and `SignalAdapter` contain
only those shapes and inverse value operations. Their equations, contracts,
and certificates remain in `SignalAdapterImplementation`, above structural
semantics. This gives the effective flow Foundation → low-level adapter
shapes/Structure → Semantics/Contracts → generic composition and adapter
certification → concrete Modules → Naming/FIRRTL.

### 7. Module certification assembly (resolved)

`RuleSchedules.certifiedLayer` now owns the mechanical construction of
schedule-backed layer certificates. A module supplies complete schedules,
child-rule coverage, its state correspondence and coverage, and its
`Implements` theorem; the constructor supplies structural existence and
uniqueness. The former `certificationForChildren` → opaque
`layerCertification` → `certifiedLayer` chain and trivial
`hasStructuralResult` forwarding theorems have been removed.

Recursive modules use the same constructor for each base and successor/node
layer. Their necessary extra step is visible where it belongs: instantiate
that layer with the previously certified recursive child and transport the
result to the recursively defined concrete structure. Direct certificates
remain only for schedule-free cases such as primitives, adapters, a childless
reduction leaf, and behavioral contract refinement.

### 8. Split large module files by reader-facing responsibility

Several useful modules are difficult to review because structure, contract,
schedules, construction, certification, laws, closure, and naming occupy one
large file. The worst current examples are `RegisterBank` (1,148 lines),
`Reduction` (1,081), `Increment` (1,069), `Add` (962), `Equality` (952), and
the three bitwise files (869 each). PicoRV ALU is 1,237 lines.

The main module file should continue to show ports, natural contract, child
instances, body/wiring, structure, public certificate, public laws, and naming
in that order. Large private schedules and refinement proofs can live in a
distinctively named sibling such as `RegisterBankCertification.lean` or
`AluCertification.lean`. Avoid generic filenames like `Implementation.lean`.
First remove duplication; otherwise splitting merely hides repeated code.

### 9. Remove `ModuleSignature` (resolved)

The unlabelled `ModuleSignature`, `ModulePorts.signature`,
`ModuleBody.signature`, and their self-only checks have been removed. No
production consumer existed. The richer labelled `ModulePorts` is now the sole
module-boundary representation.

### 10. Regression aggregation and coverage (resolved)

Bitwise OR now has symmetric focused coverage. Shared PicoRV control and
datapath inputs live under `Examples/Fixtures/`, while files under `Checks/`
are actual regression roots. `SileanExamples.lean` retains its explicit import
list, and `make check-example-imports` verifies that every `*Checks.lean` file
appears in it. Closed FIRRTL rendering is used at concrete emitter boundaries;
ordinary rendering remains available for intentional blackboxes.

### 11. Reduce documentation to current architecture and current direction

`docs/Architecture.md` is 803 lines and contains historical performance
experiments (“Forward-propagation experiment”, “All-child facts experiment”,
and an ALU selector-chain trial). `Roadmap.md` contains a long sequence of
“Completed ...” narratives. Both are useful archaeology but poor guides to the
current design, and they conflict with the stated preference not to preserve
history merely because it exists.

Recommendation:

- rewrite `Architecture.md` as a concise description of the current semantic
  and certification path, with one worked composite example;
- reduce `Roadmap.md` to destination, established capabilities, current
  constraints, and genuinely planned work;
- keep `SourceMap.md` as the short navigation document and verify every path;
- retain focused design documents only when they explain a still-live
  abstraction or decision.

The former PicoRV32 inventory, hierarchy, and top-level planning documents
were consolidated into `PicoRV32Plan.md` after this audit.

### 12. Minor repository hygiene

Ignored swap files, `__pycache__`, and cocotb `results.xml` files are present in
the working tree. `.gitignore` correctly prevents them being committed. They
are not a source problem, but removing them locally before sharing the tree
will make filesystem-wide reviews less noisy.

The Nix flake follows an unpinned `nixpkgs-unstable` input in source, while
`flake.lock` pins the actual revision. That is normal. The shell visibly marks
itself with `[silean]`, and the Makefile gives clear per-design FIRRTL,
SystemVerilog, and test targets.

## Layer-by-layer file assessment

This section records the disposition of every source area so that “not
mentioned above” does not mean “not reviewed.”

### Foundation

- `SignalType`, `SignalMap`, `SignalSelection`, `Enumeration`, and
  `DeriveEnumeration` form a coherent dependent, labelled signal foundation.
  `ListIndex`, `DependentList`, and `EnumeratedMap` have broad real use and are
  not wheel-reinventing cruft in this context.
- `BitVector` is the shared LSB-first arithmetic interpretation used throughout
  the hardware library. Generic execution traces live under `Semantics`,
  partial expected values under `Contracts`, and FIFO-only circular-buffer
  arithmetic beside the FIFO implementation rather than in the foundation.
- `ModulePorts` is the single, appropriately small labelled boundary type.
- `StructuralState` is tiny but justified: it is the recursively derived state
  shape shared by structural semantics and certifications.

### Structure and semantics

- `Primitive`, `ModuleBody`, and `ModuleStructure` have clean ownership:
  primitive equations, uninstantiated parent layer, then recursive concrete
  hierarchy.
- `StructuralEquations` is the semantic center and should remain independent
  of schedules.
- `StructuralDependency` and `StructuralExecution` are useful separate
  developments: uniqueness support and finite relational execution.
- Splitter and combiner are structural adapters rather than behavioral
  primitives; their special treatment in structure and FIRRTL is consistent.

### Contracts

- `CycleContract`, `CycleEvaluation`, and `CycleImplementation` cleanly
  separate behavioral declaration/evaluation from structural refinement.
- Layer certification consumes exact child contracts and certified child
  structures directly; no second bundled-child representation remains.
- `CycleBlackbox` is small and honest about its assumed boundary.
- `ResetContract`/`ResetImplementation` are a genuinely different exact-trace
  abstraction, not a duplicate cycle contract.
- `FifoPortContract`, `FifoContract`, `FifoCycleBehavior`, and
  `FifoCycleRefinement` layer interface events, abstract queue traces, reusable
  exact FIFO behavior, and refinement sensibly. Their filenames and namespaces
  are now consistent.

### Interfaces and primitives

- `ValidReady` and `FifoPorts` are useful boundary abstractions. “Interface” is
  reserved for behavior-bearing valid/ready views, while FIFO ports remain
  connectivity.
- The primitive files are repetitive but appropriately small and one-per-leaf.
  `PrimitivePorts` shares the common port enumerations. Primitive
  `outputReads` is necessary dependency metadata for structural uniqueness;
  it is not a behavioral contract hidden in structure.
- Primitive naming is safely indexed by the exact primitive operation, so a
  supported primitive cannot accidentally be emitted as another operation.

### Generic composition

- `SignalLayout`, `SignalAdapter`, `SignalAdapterImplementation`, and
  `SignalLogic` are useful generic aggregate machinery.
- `LeafwiseComposition` is valuable, but its abstraction boundary should be
  extended enough to remove the bitwise copies.
- `Reduction` is conceptually useful and naturally larger because it proves
  balanced-tree facts and handles empty/leaf/node cases. Its concrete Constant
  dependency and repeated certification cases should be cleaned up.
- `FifoSerialComposition` and `FifoSerialRefinement` are useful builders rather
  than standalone hardware modules. Naming should move out of the former.

### Concrete modules

- The arithmetic chain (`HalfAdder`, `FullAdder`, `Add`, `AddSub`,
  `Increment`) has natural public contracts and sensible hardware hierarchy.
  Its main issue is proof volume and inconsistent assembly boilerplate.
- Aggregate logic (`Constant`, `All`, `Equality`, `Mask`, bitwise operations,
  `Mux`, `CombMuxTree`, `BinaryToOneHot`, `VectorConcat`, `VectorSplit`) is
  structurally generic and matches the project direction. The bitwise copies
  are the clear outlier.
- State modules (`Register`, `EnabledRegister`, `ResetRegister`,
  `EnabledResetRegister`, `EnabledResetCounter`, `RegisterBank`) preserve state
  ownership in the natural child. RegisterBank is a strong but oversized
  compositional example.
- FIFO organization is sensible: one-entry implementation, serial-depth
  builder, pointer/register-bank FIFO, exact cycle behavior, and abstract FIFO
  certification are distinct. `FifoCertified` and the one-entry/serial
  certified siblings are short public bridges rather than duplicate modules.
- `FifoPointerControl` is combinational and correctly keeps reset outside it.

### PicoRV example

- `Decoder`, `Memory`, `Control`, and `Datapath` currently provide reviewed
  contract boundaries; `Regs` and `Alu` now have concrete certified structures.
- `AluLaws` usefully keeps public behavioral consequences separate from the
  already-large ALU implementation.
- `PicoRV` plus `PicoRVSchedule` establish the configured top-level composition
  against blackbox child contracts. They must continue to be described as
  staged composition, not a synthesized or closed verified CPU.
- The control/datapath fixture files and many narrowly split check files make
  the PicoRV regression area harder to browse than the source. Group shared
  fixtures explicitly and consider one check file per child contract unless
  compile time forces the current split.

### Naming, FIRRTL, emitters, and tests

- `ModuleNaming`, primitive/adapter naming, and FIFO port naming maintain the
  desired separation between semantic structure and emitted labels.
- `Traversal` correctly collects child-first definitions and keeps every
  occurrence so `Render` can diagnose one key naming different bodies.
- `Render` performs useful executable validation and handles hierarchical tuple
  field names. Its lack of a semantic preservation theorem is known.
- `Emit` is a suitably small CLI helper. The four emitter executables are a
  reasonable configuration mechanism and consistently require closed
  hierarchies.
- The root and per-test Makefiles are simple and appropriate. Cocotb tests use
  real clocks and edge/read-only phases. Both FIFO regressions reset first and
  use randomized valid/ready streams followed by a checked drain.

## Remaining cleanup

The architectural duplication, regression gaps, obsolete `ModuleSignature`,
and documentation overlap found by this audit are resolved. Future splitting
of a large module file should be driven by reader clarity: keep ports,
contract, structure, public certificate, laws, and naming easy to find, and
move only genuinely obstructive private certification detail into a uniquely
named sibling file.
