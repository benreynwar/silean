# Silean roadmap

## Destination

Silean is an experiment in writing structural hardware and useful correctness
proofs in the same Lean program. The design should remain close enough to a
conventional hierarchical HDL that hardware engineers can recognize ports,
instances, wiring, state, and reusable modules.

A structure denotes simultaneous equations. Proofs establish that those
equations have one result and that every result satisfies an independently
written behavioral contract. FIRRTL is emitted directly from the same
structure.

The long-term application is a small RV32I processor based on a fixed,
source-faithful PicoRV32 configuration. Its public theorem should concern
observable memory-mapped-I/O and termination or trap behavior, with stronger
memory-transaction correspondence available as a supporting property.

## Established capabilities

The repository currently has:

- recursive bit, vector, and named-tuple signal shapes;
- finite symbolic labels and dependently typed signal maps;
- total same-shaped wiring and recursively owned module structures;
- primitive, splitter, combiner, composite, and explicit blackbox leaves;
- simultaneous structural equations expressed by one recursive `HierStep`;
- finite structural execution and an executable no-blackbox check;
- exact cycle contracts with independent behavioral state;
- contract-independent structural-rule schedules establishing existence and
  complete hierarchy-wide uniqueness, with cycle contracts contributing
  fine-grained dependency rules when available;
- concise authoring declarations for ordinary fixed modules, with recursive
  and generated designs deliberately retaining ordinary Lean;
- a reader-facing `Foo.lean` / `FooDerived.lean` interface and private
  `Internal/` structure and verification files where that separation helps;
- reset-synchronized trace contracts with ternary output expectations;
- latency-independent valid/ready FIFO contracts;
- direct FIRRTL generation, CIRCT/Verilator lowering, and cocotb regression;
- reusable registers, muxes, logic, arithmetic, adapters, counters, register
  banks, and FIFO implementations; and
- a public proof that the pointer FIFO satisfies its bounded abstract FIFO
  contract after reset.

The configured PicoRV32 hierarchy is fully structural and recursively
blackbox-free. Decoder, memory, datapath, control, register file, and their
children have closed certified structures. The top-level hierarchy has
existence and uniqueness proofs. It does not yet have the processor-level
architectural refinement theorem described below.

The repository now gives its main concerns explicit sibling boundaries:
`Silean/` contains the reusable framework, `RV32I/` the dependency-free clean
architecture, `PicoRV/` the processor client and its proofs, and `SailBridge/`
the optional generated-Sail validation package. Documentation and regression
trees remain shared and project-scoped under `docs/` and `tests/`.

## Current constraints

- Signal semantics are two-state Boolean semantics.
- A single global clock is implicit throughout the hierarchy.
- Reset is synchronous and module-specific.
- The formal correctness boundary ends at `ModuleStructure`; FIRRTL and
  SystemVerilog are regression-tested but not proved semantics-preserving.
- Blackboxes are explicit assumptions and must be absent from a closed design.
- Contract state should be natural for specification and need not reproduce
  the structural state tree.
- High-level modules need not expose exact cycle contracts when a temporal or
  observational contract is more appropriate.
- New helpers should capture genuinely repeated proof or construction
  patterns, not special cases for one module.

## Near-term work

### Completed framework migration: structural authoring identity

> **Status: completed and verified 2026-09-20.** This section retains the
> architectural rationale and migration record for future maintenance.

The former `CircuitDescription` representation used emitted `SourceName`s as
the identities of parent inputs, child instances, and child output ports. The
typed builder knew the original endpoints but erased them to names when it
constructed a description. Consequently, the correspondence soundness proof
needed `Description.UniqueNames` and a collection of per-module boundary-name
theorems to recover typed endpoint identity from textual-name equality.

This is the wrong separation of concerns. Emitted names are metadata and may
be rejected for collisions by an emitter, but name uniqueness should not be a
precondition for the circuit's structural semantics or behavioral proofs.
The chosen direction is to preserve the existing ordinary monadic and dynamic
authoring interface while assigning stable description-local structural IDs:

- parent input and output IDs follow canonical boundary enumeration;
- a fresh child ID is allocated when a child is placed;
- child input and output IDs follow that child's canonical port enumeration;
- connections refer to these structural IDs; and
- `SourceName` remains alongside the structural identity solely as emission
  and reader-facing metadata.

An indexed builder whose type-level instance context grows after every child
placement was considered. Although possible, it would require indexed bind,
weakening of earlier references, special handling of conditional or recursive
generation, and substantial changes to every reusable placement API. The
structural-ID approach retains dynamic placement without making names into
semantic keys.

The structural-identity implementation makes `CircuitDescription`
correspondence and soundness independent of `SourceName`. Its completed ledger
is:

- [x] establish that early name erasure, rather than missing automation, is
  the source of the repeated uniqueness proofs;
- [x] choose description-local structural IDs over an indexed builder, while
  retaining the ordinary monadic and dynamic placement interface;
- [x] bound the migration to reusable Silean code and explicitly defer
  PicoRV repair;
- [x] define the structural identity types and attach identities to
  description ports, children, and sources without changing public placement
  ergonomics;
- [x] make both the dynamic `Builder` and `ofCompositeNaming` assign the same
  canonical identities;
- [x] replace name-based source injectivity and entry matching in
  `CircuitDescriptionSoundness` with structural-identity arguments;
- [x] replace `Description.UniqueNames` in `Corresponds` with only the
  structural validity needed for IDs to resolve with the correct signal
  types;
- [x] replace the invalid-description sentinel's reliance on duplicate names
  with explicit construction validity, preferring `buildResult` wherever a
  failed build must remain observable;
- [x] migrate the reusable Silean modules and focused authoring/soundness
  tests;
- [x] add a regression showing that duplicate emitted names do not invalidate
  structural semantics, while emission still reports the collision; and
- [x] remove obsolete per-module `portNames_nodup` proofs and other naming
  lemmas that existed only to establish semantic correspondence.

`Corresponds` needs no separately authored well-formedness proof: its exact
equality with `ofNaming` establishes that every structural source ID came from
the typed production body and therefore resolves at the required signal type.
The `Description.valid` flag has the narrower role of distinguishing a
successful description from the convenience `build` failure sentinel;
`ofNaming` always produces a valid description, so that sentinel cannot obtain
a correspondence certificate.

Boundary naming remains emission metadata. Per-module projection equations and
name-uniqueness theorems were removed because they had no remaining consumers;
they should be reintroduced only if a concrete emission-facing API needs them.
`ModuleNaming.withPorts` remains an actively used construction helper.

The earlier broad goal to standardize boundary naming across handwritten
recursive modules is superseded. The completed `Mask` normalization remains,
but the proposed repository-wide theorem expansion was unnecessary once
structural identity removed names from semantic matching. No temporary
compatibility API remains after the migration.

PicoRV migration and repair are explicitly outside this framework goal. The
`PicoRV/` client may temporarily stop building while the reusable authoring
base changes. Do not distort the new core interface or delay the migration to
keep that subtree compiling; update PicoRV in a later, separate pass once the
base representation has settled. The reusable `Silean` library and the full
`SileanTests` target pass together (328 jobs, verified 2026-09-20), so HTFFT
multiplier work can resume on the new foundation.

### Generalize structural-rule certification

> **Status: completed and verified 2026-09-20.** `lake build Silean` passes
> 262 jobs and `lake build SileanTests` passes 343 jobs. PicoRV remains outside
> this migration by design.

Structural existence and uniqueness now have a contract-independent owner.
Boundary-only `ModuleStructuralRules` describe dependencies, while
`ModuleStructuralCertification` and `ModuleStructuralRuleCertification`
connect those rules to concrete structures. Cycle contracts automatically
erase to fine-grained structural rules; any structurally certified module also
has a conservative whole-module rule.

The migration ledger is:

- [x] define boundary structural-rule specifications, exact output coverage,
  and concrete rule certification;
- [x] move rule occurrences, schedules, semantics, existence, and uniqueness
  to the contract-independent structural layer;
- [x] derive fine-grained structural rules and certifications from existing
  cycle contracts without changing ordinary cycle authoring syntax;
- [x] keep `module_rule_schedules` canonical for cycle certification and make
  `module_complete_schedule` genuinely contract-independent;
- [x] add automatic whole-child packaging and a standard constructor for
  certifying separately declared composites from complete schedules;
- [x] remove unreferenced compatibility projections and duplicated
  cycle-specific derivation lemmas rather than retaining parallel APIs;
- [x] structurally certify `CarrySaveLayer` and recursive `CarrySaveTree`
  without giving either custom relational contract a duplicate deterministic
  behavioral contract; and
- [x] run focused authoring regressions followed by the complete reusable
  Silean test target and record the verified result.

The CarrySaveLayer validation also introduced generic `VectorReindex`, a pure
wiring module containing one splitter and one combiner. The layer now forms a
simple flat intermediate vector and reindexes it into sum/carry interleaving;
this preserves the intended hardware order while keeping dependent recursive
routing out of the parent schedule proof.

### Build the reusable HTFFT multiplier foundation

> **Status: in progress.** `PartialProductRow`, `CarrySaveAdder`,
> `CarrySaveLayer`, `CarrySaveTree`, and `UnsignedMultiply` are complete. The
> next multiplier-stack dependency is `ConditionalNegate`. The unsigned
> milestone is verified by `lake build Silean` (266 jobs) and
> `lake build SileanTests` (348 jobs) on 2026-09-20.

The carry-save layer has a natural fixed-width contract and a single indexed
structural implementation containing one `FullAdder` per bit. Its certified
public theorem preserves the three-input unsigned sum modulo the vector width;
zero-, one-, and multi-bit checks cover behavior, hierarchy closure, and RTL
shape. An authored `ModuleBuilder` duplicate is intentionally omitted because
the indexed `module_design` already expresses the hardware directly.

`CarrySaveLayer` and `CarrySaveTree` now have custom relational contracts,
indexed/recursive structures, contract-independent structural certifications,
direct relational correctness theorems, closed hierarchy checks, and RTL-shape
tests. The tree fixes the evident zero-, one-, and two-operand representations
while leaving larger output pairs abstract; a parent consumes only preservation
of the collection total and does not learn the internal grouping. This
validates custom contracts as usable compositional module boundaries without
introducing a parallel deterministic `ModuleCycleContract`.

`UnsignedMultiply` is the first downstream validation of that interface. It
constructs one ordinary partial-product row per right-operand bit, reduces the
rows through `CarrySaveTree`, and resolves the last two operands with `Add`.
Its independent natural contract states exact multiplication at the combined
operand width; its cycle certification proves every structural realization
satisfies that contract, including zero-width and asymmetric-width cases.
Closed-hierarchy and RTL-shape tests cover the composition. The provisional
full stack and its evolving proof obligations remain tracked in
`HTFFT/Plan.md`.

The two principal remaining processor proofs are complementary:

```text
configured upstream picorv32.v
        equivalent to
certified Silean PicoRV structure
        refines
clean RV32I execution
```

Neither link should be treated as evidence for the other. The source-equivalence
proof establishes that the hardware we certified is the selected upstream
core; the architectural-refinement proof establishes what that certified
hardware means.

### Prove equivalence with the configured PicoRV Verilog

Establish a formal connection between the exact `picorv32.v` revision and
configuration recorded in
[`docs/picorv/PicoRV32Plan.md`](docs/picorv/PicoRV32Plan.md) and the Silean
PicoRV structure. The existing scoped `mem_valid` equivalence check covers only
part of this goal. The precise equivalence statement, proof boundary, and
approach remain to be designed and reviewed before implementation.

### Refine the Silean PicoRV model to RV32I

The next processor milestone extends the verification stages in
[`docs/picorv/PicoRV32Plan.md`](docs/picorv/PicoRV32Plan.md):

1. define the external memory environment and identify the memory-mapped-I/O
   address region outside the processor core;
2. define observable completed bus transactions, retirement, trap, and
   termination without adding emitted RVFI hardware;
3. relate reachable PicoRV contract state to a committed RV32I state plus
   explicit in-flight instruction and memory-operation information;
4. prove one complete ADDI slice, including memory stalls and stuttering
   implementation cycles;
5. extend the argument to loads and stores before generalizing across the
   instruction set; and
6. derive the public I/O-trace theorem, retaining ordinary-memory
   correspondence as a stronger supporting property where required.

The clean `RV32I/` model is the direct architectural target. Its independent
agreement with generated Sail remains isolated in `SailBridge/`; PicoRV proofs
should not import generated Sail definitions. Safety and progress are
separate: the trace refinement must be accompanied eventually by an explicit
responsiveness or fairness assumption for memory.

### Keep proof interfaces small

Schedule derivation, child-contract matching, and wiring normalization already
remove much of the mechanical certification work. Continue reducing repeated
proof plumbing only when a helper improves both a module's public theorem
interface and real downstream proofs. Do not hide module bodies, wiring, state
correspondence, module-specific reasoning, or the final behavioral argument
merely to reduce line count.

### Add balanced priority selection

Introduce a reusable priority-mux tree for ordered selector/value choices.
Its public authoring interface should use ordinary Lean values, such as a
`Fin count` function returning `(Net .bit × Net element)`, with an explicit
default value. The contract must preserve the current total behavior: the
first true selector wins when selectors overlap, and the default wins when
none are true. Keep the balanced recursive implementation under `Internal/`.

Use this abstraction to replace explanatory-but-deep mux chains such as the
ALU result and comparison selections after its interface has been reviewed.
Do not implement it by encoding one-hot controls back into a binary address;
a separate one-hot selection module can be added later if a design genuinely
has one-hot controls and benefits from an OR-tree implementation.

### Revisit elaboration performance

Some of the larger decoder and top-level checks remain expensive enough to
interrupt interactive work. Profile those files before changing proof APIs,
and prefer improvements to shared normalization or elaboration behavior over
module-specific shortcuts.

## Longer-term work

- Prove a semantics-preservation bridge from the supported closed
  `ModuleStructure` subset to emitted FIRRTL, or validate a smaller checked
  backend representation if that gives a clearer theorem.
- Add contract forms for other useful temporal abstractions as real designs
  demand them.
- Explore whether memory arrays deserve a structural primitive only when a
  design requires one; current plans do not assume it.

## Completion standards

A feature is complete only when its public structure and natural contract are
clear, the relevant existence or non-vacuity condition is proved, reusable
proofs do not depend on hidden child implementations, documentation states the
actual correctness boundary, and the appropriate Lean and generated-hardware
regressions pass.
