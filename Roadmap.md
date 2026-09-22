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
- [x] run focused authoring regressions followed by the complete reusable
  Silean test target and record the verified result.

### Separate general arithmetic from carry-aware primitives

> **Status: complete and verified 2026-09-21.** `lake build Silean
> SileanTests` passes 3,403 jobs. PicoRV migration remains deliberately outside
> this work.

The former `Add` and `AddSub` names described equal-width, carry-aware building
blocks rather than the arithmetic interface needed by fixed-point clients.
They are now `AddWithCarry` and `AddSubWithCarry`. Their emitted module
identities use the same explicit terminology. General structural `Add`, `Sub`,
and runtime-selectable `AddSub` modules accept independent operand widths,
static signedness for each operand, and a static choice between wider and
truncating output. Their contracts interpret inputs as ordinary integers,
perform ordinary integer arithmetic, and encode only at the result boundary.

The implementation ledger is:

- [x] move and rename the equal-width carry-aware modules;
- [x] add reusable Boolean module-specialization parameters and rendering;
- [x] prove vector layouts implement native sign or zero extension;
- [x] define natural contracts before the new structures;
- [x] build and certify structural `Add`, `Sub`, and `AddSub` hierarchies using
  only public facts about their children;
- [x] make authoring arithmetic operators thin placements of those real
  modules rather than inline pseudo-module recipes;
- [x] migrate reusable carry-dependent consumers to `AddWithCarry`;
- [x] cover signedness combinations, unequal and zero widths, extension,
  wrapping, both runtime selector values, and FIRRTL emission in focused tests;
- [x] run the complete reusable Silean regression and update this status.

No deprecated aliases preserve the misleading old meanings of `Add` or
`AddSub`: the corrected general modules intentionally reclaim those exact
names, so both APIs cannot coexist under them. Reusable clients were migrated
directly. PicoRV may be repaired separately once the base hierarchy settles.

### Specify fixed-point FFT arithmetic independently of hardware

> **Status: pure butterfly specification implemented and focused checks
> passing 2026-09-20.** Hardware construction and the numerical bound proof
> remain later milestones.

The pure specification layer under `HTFFT/FixedPoint`, `HTFFT/Butterfly`, and
`HTFFT/Fixed` does not import Silean hardware definitions. It represents
fixed-point values as scaled `Int`s with explicit
component width and fractional-bit count, exact `Rat` decoding, selectable
rounding, and explicit two's-complement wrapping. Its initial butterfly policy
uses fused full-precision complex products, round-to-nearest with ties to even,
one-bit output growth, and explicit wrapping guarded by a named no-overflow
predicate.

The ordinary rational butterfly is separate from the fixed-point function. A
componentwise local-error predicate states the intended shape of the later
accuracy theorem. The old VHDL informed the arithmetic review but is not
maintained as a second Lean model or regression target. `lake build HTFFT
HTFFTTests` passes 10 jobs.

### Prove the exact recursive radix-two FFT correct

> **Status: complete 2026-09-21.** This recursive theorem is now also the
> reference used to certify the bit-reversed layered network below.

Mathlib is pinned to `v4.32.1`, matching the project toolchain. The standalone
`HTFFT.Exact` namespace represents a depth-indexed vector naturally as
`Fin (2 ^ depth) → ℂ`. Its public indexing operations use Mathlib's finite
equivalences for even/odd splitting, first/second-half concatenation, exact-width
bit reversal, and the canonical `Fin (2 ^ depth) ≃ ZMod (2 ^ depth)` DFT
boundary.

The recursive DIT transform splits source indices into `2*k` and `2*k+1`, then
places sums at `k` and differences at `k + 2^depth`. Public first-half and
second-half Cooley--Tukey theorems reindex Mathlib's DFT sum and prove the
required `stdAddChar` identities. Their induction proves
`radix2_agreesWithDFT : Radix2AgreesWithDFT`. Exact impulse checks cover sizes
two, four, and eight.

### Define the exact hardware-shaped FFT network

> **Status: exact foundation complete 2026-09-21.** No fixed-point FFT network
> or Silean FFT hardware has been introduced yet.

`HTFFT.Exact.Layered` now describes the pure iterative topology independently
of clocks, memories, and fixed-point arithmetic. A public layer position names
the contiguous group, sum/difference branch, and shared within-half offset.
Stage zero pairs adjacent values; each following stage doubles the spacing and
group size. Each layer uses the matching exact twiddle, and the complete
network is input bit reversal followed by stages in ascending order with no
final permutation.

The ordered stage list remains explicit. `LayerBoundary`, `layeredPrefix`, and
`layeredFFT_split` prove that any `take`/`drop` boundary preserves the complete
pure transform, permitting a future hardware proof to assign the prefix and
suffix to combinational and memory-backed organizations.

The correctness proof shows that bit reversal separates even and odd inputs,
every nonfinal prefix acts independently on the resulting halves, and the
final layer has exactly the recursive FFT's indexing and twiddle selection.
This yields `layeredFFT_eq_radix2` and the pointwise
`layeredFFT_agreesWithDFT`. Executable indexing and split checks plus exact
impulse examples cover depths zero through three. The combined `HTFFT`,
`HTFFTTests`, `Silean`, and `SileanTests` build passes 3,798 jobs, verified
2026-09-21.

### Build the first certified HTFFT hardware arithmetic block

> **Status: complete and verified 2026-09-21.** The combined `lake build
> Silean SileanTests HTFFT HTFFTTests` gate passes 3,866 jobs.

The project-specific pipelined signed complex multiplier now lives under
`HTFFT/Silean/PipelinedSignedComplexMultiply/`, rather than in the reusable
Silean module catalog. Its natural trace contract specifies one fused
nearest-even rounding step after each full-precision real or imaginary
numerator. Four equal-latency signed multipliers feed certified extended
signed subtraction and addition. An optional synchronized register can delay
the combined real and imaginary numerators before the two signed round/shift
blocks.

Structural certification and the all-time delayed trace theorem are complete.
The parent proof consumes only public child structural and execution facts and
extracts all four multiplier traces from the same parent witnesses to preserve
alignment. A separate fixed-point theorem connects decoded outputs to
`HTFFT.Butterfly.Fixed.multiplyRounded` under the binary-point relation and
representability hypotheses. Focused regressions cover arithmetic, ties,
zero-width and excessive-discard boundaries, latency, placement, hierarchy,
and FIRRTL shape. The next hardware step is the complete packed butterfly
contract and structure; it should use this multiplier rather than reopen its
internal product pipeline.

### Build the project-specific pipelined fixed-point butterfly

> **Status: complete and verified 2026-09-21.** The combined `lake build
> Silean SileanTests HTFFT HTFFTTests` gate passes 3,876 jobs.

This milestone first makes fixed-latency behavior easier to state and compose
without exposing either contract state or structural state. The reusable
foundation now has a state-free `BoundaryStep`, a `BoundaryTrace` consisting
of a sequence of those steps, and a standard projection from the existing
state-threaded `Trace` and `ModuleStructure.Executes` semantics. This is an
observable specification layer, not a replacement for `CycleStep`,
`HierStep`, or structural execution.

The remaining ledger is:

- [x] define the general fixed-latency relation over `BoundaryTrace` and its
  serial and synchronized-parallel composition laws;
- [x] validate that interface on `ShiftRegister`,
  `OptionalShiftRegister`, keeping their contracts natural and
  implementation-independent, and `PipelinedSignedMultiply`;
- [x] provide reusable synchronized child-execution observation where the
  structural proof pattern genuinely repeats;
- [x] finish the complex multiplier's aggregate optional pre-rounding stage,
  trace proof, fixed-point bridge, public API migration, and regressions;
- [x] freeze the butterfly width, rescaling, narrowing, wrapping, and
  representability policy before its structural implementation;
- [x] define the complete butterfly contract and reviewed pipeline
  configuration;
- [x] build and certify the structural butterfly using only public child
  interfaces; and
- [x] prove agreement with the pure fixed-point butterfly and cover every
  pipeline configuration, latency, hierarchy, and FIRRTL shape in focused and
  combined regressions.

The selected boundary policy keeps the data binary point fixed. The fused
complex product rounds once, is explicitly narrowed or wrapped to the input
component width, and the final signed Add/Sub grows each component by exactly
one high bit. No low bits are discarded after that final Add/Sub. The
unconditional trace theorem is bit-accurate to the pure wrapped butterfly;
the separate `NoOverflow` bridge identifies the decoded output with the
pre-wrap pure result.

Do not broaden this milestone to an FFT layer, unrolled network, or streaming
memory organization. Those remain later stages after the butterfly arithmetic
and its temporal composition interface are stable.

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
