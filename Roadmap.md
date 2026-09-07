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
observable memory-mapped-I/O and termination/trap behavior, with stronger
memory-transaction correspondence available as a supporting property.

## Established capabilities

The repository currently has:

- recursive bit, vector, and named-tuple signal shapes;
- finite symbolic labels and dependently typed signal maps;
- total same-shaped wiring and recursively owned module structures;
- primitive, splitter, combiner, composite, and explicit blackbox leaves;
- simultaneous structural equations and finite structural execution;
- an executable, proved-correct recursive no-blackbox check;
- exact cycle contracts with independent behavioral state;
- contract-only proof schedules establishing structural existence and
  uniqueness without defining circuit meaning;
- proof-producing schedule tactics that derive kernel-checked schedules and
  child-rule coverage from an explicit, module-specific rule order;
- concise authoring declarations for ordinary fixed ports, structures,
  contracts, schedules, and certification assembly, with recursive and
  generated designs deliberately retaining ordinary Lean;
- parametric certified layers whose proofs use child contracts rather than
  child implementations;
- reset-synchronized trace contracts with ternary output expectations;
- latency-independent valid/ready FIFO contracts;
- direct FIRRTL generation, CIRCT/Verilator lowering, and cocotb regression;
- reusable generic registers, muxes, constants, equality, reductions,
  decoders, vector layouts, mux trees, register banks, counters, arithmetic,
  and bitwise logic;
- one-entry, serial-depth, and pointer/register-bank FIFOs; and
- a public proof that the pointer FIFO satisfies the bounded abstract FIFO
  contract after reset.

The most developed hardware example is the generic pointer FIFO. The largest
in-progress design is the configured PicoRV32 port: all five direct child
contracts and the typed top-level blackbox composition exist, while only the
ALU and register-file children currently have closed certified structures.

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

### Decouple aggregate naming from structural hierarchy

`SignalType` deliberately defines connection compatibility by shape rather
than by emitted field names. Preserve that foundation: do not add FIRRTL names
or stable textual field identities to structural types merely to make FIRRTL
whole-bundle connections type-check.

Instead, teach the FIRRTL emitter to bridge structurally equal aggregates whose
naming trees differ. A structural connection remains one connection in Lean,
but emission recursively pairs corresponding components by position and emits
leaf connections where necessary. Bits connect directly; vectors may connect
as a whole when their recursive naming agrees and otherwise recurse by index;
tuples may connect as a whole when their field naming agrees and otherwise
recurse by field position. This must also handle vectors of tuples and other
nested combinations.

Proceed in stages:

1. **Prove the emission approach with focused checks (completed).** Connection
   rendering now retains both endpoint references and their
   `SignalTypeNaming`. Differently named flat tuples, nested tuples, and vectors
   of named tuples are connected recursively by structural position, while
   matching naming trees retain one whole-aggregate connection. Focused checks
   cover each case, and all five generated regression circuits are accepted by
   `firtool`.
2. **Give generic definitions canonical internal naming (completed).** A register, mux,
   adapter, FIFO storage element, or other shape-polymorphic module should be
   one structural definition parameterized by `SignalType`, with positional
   names for its emitted internal boundary. A named parent boundary connects to
   it through the emitter's recursive bridge; different payload schemas must
   not create different generic hardware definitions solely because their
   field spelling differs. `Register` and `Mux` now follow this rule. The
   mux's complete Mask/BitwiseOr hierarchy is canonical internally while an
   optional authored naming tree is retained only at its public boundary.
   SignalAdapter, unary and binary leafwise composition, Reduction, Constant,
   Mask, BitwiseAnd/Or/Xor, Equality, All, and Any now construct and certify
   their reusable hierarchies from `SignalType` alone. The PicoRV decoder's
   named thirteen-field aggregate uses thin named-boundary wrappers whose sole
   children are those same positional tuple adapters; authored labels never
   specialize the generic adapter definition. VectorConcat, VectorSplit,
   VectorSlice, CombMuxTree, EnabledRegister, ResetRegister,
   EnabledResetRegister, EnabledResetCounter, and RegisterBank now follow the
   same rule. Their structures, contracts, schedules, and certifications take
   signal shapes only; optional `SignalTypeNaming` values affect emission only.
3. **Remove naming schemas from proof and structural APIs (completed).**
   Schemas no longer propagate through reusable structures, contracts,
   schedules, certifications, or child hierarchies. Flat tuples, nested tuples,
   and vectors of tuples pass through canonical generic hierarchies using
   emitter-side field bridging. Focused checks include a named nested payload
   through a register bank, and emitted register and register-bank hierarchies
   are accepted by `firtool`.
4. **Migrate FIFO hierarchies (completed).** `OneEntryFifo`,
   `SerialDepthFifo`, and the pointer/register-bank FIFO now construct and
   certify one canonical hierarchy from `SignalType` alone. Authored nested
   payload names are attached separately by emission metadata and propagated
   through their storage children. Focused render checks cover all three FIFO
   forms; generated one-entry, serial, and pointer FIFOs are lowered with
   `firtool` and exercised by cocotb.
5. **Reassess the author-facing schema abstraction (completed).** The duplicate
   structural schema tree and `NamedSignalSchema` wrapper have been removed.
   `SignalSchema` is now only a thin authoring name for `SignalTypeNaming`,
   indexed by the ordinary `SignalType`. A `signal_schema` declaration produces
   one labelled `SignalMap`, its aggregate type, one hierarchical naming tree,
   and a typed per-field schema accessor. Nested and parameterized schemas use
   the same representation, with no schema data in hardware or proof APIs.

The full Lean build, FIRRTL lowering, and cocotb suite are the regression gate
for further naming changes.

### Named cycle-rule values (resolved)

Cycle rules now use label-preserving `SignalGroup` values throughout. The
previous representation forced large rules to
repeat explicit `SignalTypes` chains, construct selections with `prepend`, and
unpack nested products through `.1`/`.2`; this was most visible in the PicoRV32
ALU.

Evaluation, schedule derivation, certification, and existing contracts consume
named groups directly. The authoring directive generates named groups rather
than positional compatibility values, and the obsolete constructors and tactic
branches have been removed. HalfAdder, generic EnabledRegister, multi-output
authoring checks, the PicoRV32 ALU, and the decoder's precise 39-of-40 trap
dependency cover the important shapes.

The separate anonymous-aggregate issue in `DecoderCaptureStage` is addressed by
a generic, label-directed view between any `SignalMap` and its canonical tuple
layout. Named values can be packed into that tuple and unpacked again, with
round-trip laws. Thin named-boundary combiner and splitter modules translate
typed labels to positional child ports; the underlying structural adapters and
their certifications remain entirely shape-based.
`DecoderCaptureStage` retains the one thirteen-field aggregate enabled
register used by the hardware, while its wiring and proof helpers refer to
meaningful field labels rather than positional aliases or nested projections.

Irregular bit organization now has a reusable structural form as well.
`VectorLayout` maps every output-vector bit to either an indexed input bit or a
Boolean constant, with a direct functional cycle contract and a closed
splitter/constant/combiner implementation. Its checks cover permutation,
duplication, truncation, sign extension, constant insertion, and the PicoRV32
J-immediate map. This keeps instruction-specific layouts as readable Lean
mapping functions while preserving an ordinary explicit hardware hierarchy.
The decoder capture stage now uses one `VectorLayout` child for its J-immediate.
Its cycle contract applies the same readable layout function, while its
certification relies only on the child's public output theorem. This replaces
the bespoke word splitter, immediate combiner, per-bit wiring, and five-way
per-index proof without exposing the generic child's implementation.

### Improve the module-authoring surface (completed)

The repository now contains enough varied modules to distinguish genuinely
repeated authoring patterns from one-off conveniences, while it is still small
enough to migrate cleanly. Before adding more PicoRV32 structures, introduce a
concise authoring surface for the mechanical parts of ports, contracts,
instances, wiring, schedules, and certification. The detailed design notes are
in [docs/FullAdderAuthoringReview.md](docs/FullAdderAuthoringReview.md).

This work must remain a surface layer over ordinary, separately named Lean
definitions. It must not merge structures with contracts, expose child
implementations to parent proofs, or force recursive and programmatically
constructed modules through syntax intended for ordinary fixed modules.

Proceed in stages:

1. **Improve the underlying APIs first.** Add the small semantic accessors and
   constructors identified by the review, including readable access to child
   outputs and parent outputs, inferred rule signatures, public primitive
   contract laws, and a compact stateless certification constructor. Test these
   improvements in handwritten definitions before adding syntax for them.
2. **Establish the lower-level generated API.** The `module_ports` pilot supports
   arbitrary signal shapes, explicit emitted-name overrides, and parameterized
   naming builders. Its original pilots included `HalfAdder` and generic,
   stateful `EnabledRegister`; `HalfAdder` now uses the unified declaration
   described below. Its ordinary generated API, focused
   diagnostics, readability, and build performance have been reviewed in
   [docs/FullAdderAuthoringReview.md](docs/FullAdderAuthoringReview.md). The
   completion pass also validates multi-parameter `VectorConcat` and the large
   PicoRV ALU boundary, and supports empty directions and multiple independent
   component-naming parameters. Modules with indexed labels and deliberate
   enumeration proofs, such as `RegisterBank`, or boundaries derived from
   another reusable abstraction, such as `Constant`, should retain ordinary
   declarations rather than being forced through this command.
   `SignalSchema` is a thin authoring name for hierarchical
   `SignalTypeNaming`, indexed by its proof-independent shape. Port declarations
   consume it only as emission metadata. `TupleField` validates typed named-field selection by wrapping
   the existing structural splitter and carrying an independent cycle proof.
   The parameterizable `signal_schema` declaration generates the label type,
   canonical `SignalMap`, aggregate `SignalType`, hierarchical schema, and
   typed per-field schema accessor. Each generated `Field` constructor is itself
   the typed field label.
   The nested structured-FIFO payload and PicoRV32
   decoder-capture aggregate validate recursive naming and larger field sets;
   FIRRTL checks use a generated witness directly through `TupleField`.
3. **Unify ordinary module design authoring.** The lower-level
   `module_instances` command selects concrete child structures and generates
   only structural objects.
   `module_child_certifications` separately selects the contracts and
   certifications available to the parent proof and proves that their structures
   match the design-side choices. Each entry supplies the child's canonical
   `certification`; its dependent type determines both the exact structure and
   chosen contract, so the declaration never repeats either one. A module's
   public `certified` bundle remains a mechanically derived convenience rather
   than the only route to its certification. `FullAdder` is split into a concise design
   file and a proof-oriented certification file; its design import closure
   contains no certification or schedule machinery.
   The second pilot adds ordinary module parameters and migrates generic,
   stateful `EnabledRegister`; its register state remains visible through the
   abstract child contract. The third pilot adds explicitly ordered indexed
   child families and migrates `RegisterBank`, replacing its repeated child
   maps while retaining the deliberate handwritten enumeration for its
   indexed parent ports. A `boundary (...) (naming := ...)` section lets such a
   module reuse that ordinary Lean boundary without forcing it into the port
   DSL. Both migrations preserve the abstract-child proof boundary. Before
   removing unnecessary top-level name overrides, they produced byte-identical
   FIRRTL for the existing structured-FIFO and register-bank emission fixtures;
   the remaining output differences are the intentional use of each declaration
   label as its default emitted family name and removal of their unneeded
   `structural` variants. Constructor parameters now derive specialization keys
   through `ToModuleParameter`, rather than repeating `.signalType` and `.natural`
   annotations at each declaration. The
   independent `module_wiring` stage presents direct
   source-oriented wiring grouped by parent outputs and child instances and
   generates the ordinary wiring, body, and concrete structure. Its pilots
   cover generic stateful `EnabledRegister` and indexed `RegisterBank`.
   For ordinary fixed modules, the self-contained `module_design` declaration
   now combines ports, child design bundles, wiring, structure, and recursive
   default naming without an author-visible chain of generated intermediate
   values. `HalfAdder` and `FullAdder` are the dependency-complete pilot.
   Their module, port, and instance names default exactly to declaration labels,
   explicit overrides are checked, their certification remains separate, and
   existing proofs continue to use the abstract child layer. Generic
   parameters, emission-key specializations, and mixed fixed/indexed child
   families are now covered by focused checks and these two real modules. The
   lower-level commands remain useful implementation machinery and for
   recursive constructions, but should not be an alternative chain of partial
   declarations for ordinary modules that fit `module_design`.
   The generic pointer FIFO is the first completed larger stateful migration.
   Its four children and all boundary wiring now appear in one `module_design`,
   while its exact cycle certification lives in a separate proof file and its
   higher-level FIFO refinement remains independent. RegisterBank now has one
   canonical structure independent of field names; its boundary, entry
   registers, combiner, and read mux receive custom names only through
   recursive emission metadata. OneEntryFifo and SerialDepthFifo now follow the
   same structural rule, so the complete FIFO hierarchy is canonical beneath
   its separately named authored boundary.
4. **Introduce cycle-contract declarations.** With the named cycle-rule
   foundation above stable, the self-contained
   `module_cycle_contract` declaration leaves natural Lean behavior
   functions and separate rule boundaries visible while generating rule
   labels, named groups, the state rule, exact output coverage,
   contract assembly, and mechanical `...Rule_holds_iff` laws. `HalfAdder`,
   `FullAdder`, and stateful generic `EnabledRegister` are the inline pilots;
   the pointer FIFO now uses the existing-rule form for its natural multi-output
   observation and whole-state transition; focused checks also cover a rule
   with several outputs. The larger PicoRV ALU
   validates the explicit whole-rule form, retaining its ordinary Lean group
   and target while the declaration handles rule identity, state, coverage,
   and assembly.
5. **Introduce schedule and certification declarations.** Keep each
   module-specific rule order and each substantive `implements` argument
   visible, while generating rule-occurrence plumbing, coverage, structural
   existence and uniqueness, and empty-state scaffolding. Parent proofs must
   continue to quantify over abstract certified children and use only their
   public contracts. Validate ordinary schedules on `FullAdder`, indexed
   schedules on `RegisterBank`, and nontrivial state correspondence on
   `EnabledRegister` or a FIFO component. `OneEntryFifo` now validates this
   split on a complete hierarchy: its hardware and natural exact-cycle
   behavior remain in the design file, its private control child and parent
   structural arguments have separate certification files, and its
   latency-independent FIFO refinement remains a distinct public proof.
   `module_rule_schedules` now covers the schedule half of this work: literal
   orders use concise `child => rule` entries, consecutive children sharing one
   rule can use `{child₁, child₂} => rule`, and `from (...)` accepts an
   ordinary Lean expression for indexed or concatenated families. It generates
   the dependent order declaration and validated `DerivedRuleSchedules`, but
   deliberately does not hide state correspondence or `implements`.
   `module_cycle_certification` now covers the final assembly: it takes those
   schedules together with explicit structural/certified children, state
   relation, coverage, and implementation evidence, then generates the reusable
   certified layer, concrete certification, derived public bundle, and projection
   lemmas. Stateful `EnabledRegister` and stateless `TupleField` established the
   basic forms. The contrasting real-module pilots are the small, stateless
   `FullAdder` and the large, heterogeneous, stateful PicoRV32
   `DecoderCaptureStage`. In both, the rule order remains visible and the actual
   correspondence and behavioral proofs remain ordinary Lean. The decoder pilot
   additionally established grouped schedules and exposed an inconsistent child
   API: reusable modules must publish `moduleStructure`, `cycleContract`, and
   `certification`, with `certified` derived from those declarations.
   `DecoderCaptureStage` is now split into a hardware/contract/naming file and
   a separate proof file, instead of one large mixed file. Its
   fixed but heterogeneous child layer now uses one self-contained
   `module_design`. The aggregate register's thirteen inputs and corresponding
   parent outputs are connected explicitly in its wiring, keeping meaningful
   hardware routing visible and removing the previous dependent source
   helpers. The authoring work also added two general escape points without
   weakening the typed foundation:
   `from (source)` embeds an ordinary typed `SignalSource` in grouped wiring,
   and `state_rule := existingRule` lets a contract retain a natural whole-map
   next-state definition. Instance emission names now use their declaration
   labels by default rather than repeating unnecessary spelling overrides.
   The pointer FIFO additionally validates the complete declaration chain on a
   generic stateful design: child certifications, output/state schedules, and
   final certification assembly are generated while its three-child state
   correspondence and behavioral argument remain explicit Lean.
   The completion pass applies the same authoring boundary to four contrasting
   reusable modules. `HalfAdder` uses literal output schedules, `TupleField`
   certifies a typed named-field adapter, `VectorConcat` combines parameterized
   generic adapters, and `RegisterBank` exercises indexed parent rules, indexed
   child families, state correspondence, and custom recursive emission naming.
   All four now keep hardware and natural contract laws in their main files and
   isolate schedule/certification construction in `*Certified.lean`. Superseded
   handwritten schedule coverage and final bundle assembly have been removed.
   Compared with the pre-authoring forms, both modules are smaller; more
   importantly, their main files expose the design without structural
   correctness proofs interrupting it.
6. **Migrate in dependency order.** After the pilots establish the design,
   migrate primitives and small combinational modules, then stateful reusable
   modules, indexed and recursive constructions where the syntax is a natural
   fit, FIFOs, and finally the PicoRV32 examples. Delete superseded helpers and
   old authoring forms during migration; this new codebase has no compatibility
   requirement that justifies carrying two ways to express the same thing.
   The first dependency-chain pass has migrated gate-level `BitMux`,
   `ResetRegister`, and `EnabledResetRegister`. Their hardware and natural
   contracts now live in concise design files, while explicit structural
   arguments live in separate certification files. The reset-register pair also validates an
   important authoring case: reset values specialize implementations but not
   their port boundaries. Such modules declare their reusable boundary once,
   then use `module_design`'s existing-boundary form instead of introducing a
   spurious value parameter into `ports`.
   The serial FIFO stack now follows the same separation at
   both levels. The generic two-child wiring is independent of concrete child
   structures, its schedules and contract-parametric proof live in
   `FifoSerialCycleCertified`, and the shared forward/backward child-input views
   are defined once by exact FIFO semantics and reused by structural and
   abstract refinement proofs. `SerialDepthFifo` keeps its natural Lean
   recursion visible in the design file, with structural cycle certification
   and capacity-indexed FIFO refinement in distinct files.
   The next dependency pass has migrated four contrasting reusable composites:
   generic `Mux`, stateful `EnabledResetCounter`, arithmetic `AddSub`, and the
   larger thirteen-child `FifoPointerControl`. Their main files use
   `module_design` and `module_cycle_contract` for readable hardware and
   natural behavior, while their `*Certified.lean` files retain the explicit
   state relations and implementation arguments. The old handwritten
   construction, schedule, naming, and bundle assembly have been removed.
   Recursive `Increment` and `Add` remain ordinary Lean internally, but expose
   the same public design and certification boundaries when used as children.
   The latest reusable-module pass moved the remaining flat files into
   per-module directories and migrated fixed composites `EqualsConstant`,
   `VectorSlice`, and `VectorSplit`. They now use `module_design`, keep their
   natural cycle contracts in the design file, and isolate certification in
   `*Certified.lean`. Recursive or generated modules `Add`, `BinaryToOneHot`,
   `CombMuxTree`, `Constant`, `Equality`, `Increment`, `Mask`, and `Register`
   deliberately retain ordinary Lean: their child families are selected by
   recursion over widths or signal shapes, so a fixed declaration would hide
   rather than clarify the construction. `All`, `Any`, `BitwiseAnd`,
   `BitwiseOr`, and `BitwiseXor` are thin specializations of generic
   constructions in `Composition/` and have no module-specific child wiring
   for the fixed-module syntax to improve. These modules nevertheless expose
   the same public `moduleStructure`, `cycleContract`, `certification`,
   `certified`, and `design` boundary. The old flat module paths and
   `Naming.namedModule` constructors have been removed rather than retained as
   compatibility APIs.

7. **Finish the migration across the whole authored design tree.** The flat-file
   pass was not a completion audit. `NamedTupleCombiner` and
   `NamedTupleSplitter` are now migrated fixed, single-child modules: their
   design, contract, schedule, and certification declarations generate the
   mechanical layer, while their explicit Lean lemmas explain only the
   label-to-position casts at the named boundary. This migration added a
   generic symbolic-output path to schedule derivation, so an `all` output group
   over an abstract `SignalMap` no longer requires a handwritten schedule. The
   contract declaration also accepts an explicit output-coverage proof for a
   dependent existing rule when coverage is propositionally, but not
   definitionally, immediate. The PicoRV inventory has now been audited by
   authoring concern rather than treating macro adoption as all-or-nothing:
   - `DecoderCaptureStage` is the one complete PicoRV example of the full
     declaration chain.
   - `Alu` and `Regs` are now complete contrasting migration cases. Their main
     files contain the natural behavior, cycle contract, and readable concrete
     hierarchy; their `*Certified.lean` files contain child certifications,
     derived schedules, state correspondence, and structural-equivalence
     proofs. The ALU exercises a large combinational graph and the register
     file exercises a stateful indexed child. Both use generated default port
     and instance names except for their externally meaningful PicoRV module
     names. Focused contract/certification checks pass, and both emitted FIRRTL
     hierarchies are accepted by `firtool`.
   - the decoder hierarchy now completes the next PicoRV authoring pass. Its
     instruction-match, immediate, instruction-summary, resolve-stage, and
     parent contracts use the port and cycle-contract declarations. The
     resolve-stage concrete layer uses `module_design`; its three unresolved
     combinational children remain explicit contract blackboxes, and its
     output/state orders are checked by `module_rule_schedules`. The two-stage
     parent is likewise a concise authored design with proof construction in
     `DecoderCertified.lean`. Its capture child is concrete while its resolve
     child now uses its concrete certified structure. The resolve structure
     retains only its three smaller combinational contract blackboxes.
   - `Control`, `Datapath`, and `Memory` now use the port and cycle-contract
     declarations while retaining their natural ordinary Lean transition and
     rule definitions. The top-level `PicoRV` shell uses `module_design` to
     show its five children and source-faithful wiring directly. All five
     children remain explicit contract blackboxes, so this authoring change
     does not strengthen its verification boundary. Because the shell has no
     parent behavioral contract yet, the generic `module_complete_schedule`
     declaration checks its contract-independent all-child-rule order rather
     than manufacturing an artificial cycle contract. Design and schedule
     proofs remain separated between `PicoRV.lean` and `PicoRVSchedule.lean`.

   Apply `module_design` to fixed concrete child layers, the cycle-contract
   declaration where it makes the natural behavioral statement clearer, and
   the schedule/certification declarations to fixed certified layers. Do not
   force derived behavioral abstractions such as FIFO cycle composition, or
   recursive/programmatically generated hierarchies, through fixed syntax.
   Remove the superseded handwritten assembly only after each migrated file has
   focused checks. This migration is complete: the inventory has an explicit
   migrated-or-intentionally-ordinary decision, its focused checks pass, and
   the full Lean regression target passes.

At every stage, inspect the expanded declarations and reject syntax that hides
the hardware or the meaningful behavioral proof. Compare the migrated module
with its previous form for clarity and line count, keep focused representative
checks near the five-second interactive target, run the full Lean build, and
confirm that FIRRTL/Verilator/cocotb regressions remain unchanged where the
module is emitted. Commit the infrastructure and successful pilots before the
broad migration so that the design decision remains reviewable.

### Replace PicoRV32 child blackboxes

The whole-tree authoring audit in step 7 above is complete. Ordinary fixed
modules now use the readable declaration form, while recursive, generated,
and generic-composition definitions retain ordinary Lean intentionally. The
next development phase can therefore replace PicoRV32 blackboxes without
carrying an unfinished authoring migration alongside that work.

Implement and certify the remaining direct children against their existing
contracts, one source-faithful subsystem at a time:

1. decoder;
2. memory interface;
3. datapath, including iterative shifts and the already-certified ALU child;
4. control state machine; and
5. the top-level hierarchy with every blackbox replaced.

The decoder now has natural contracts for its 14-register capture stage and
45-register resolve stage. Both stages now have certified concrete structures,
and the certified parent composes those certifications. The resolve stage's
combinational instruction-match, immediate, and summary boundaries remain the
only internal decoder blackboxes; they have natural zero-state cycle contracts
and focused checks. Its equivalence proof preserves the verified pre-edge
dependencies and reset priority described in
[docs/PicoRV32Plan.md](docs/PicoRV32Plan.md). The next decoder work is to replace
those three smaller blackboxes with concrete certified implementations.

Reusable `VectorSlice` and `EqualsConstant` modules now provide the recurring
field-extraction and fixed-pattern comparisons needed by decoder structures.
The generic balanced reduction machinery now directly supports both the
certified `All` (AND/true) and `Any` (OR/false) Boolean specializations; decoder
summary logic can use `Any` instead of hand-built OR chains.
Both have natural contracts and closed certified implementations; decoder code
should use these modules instead of rebuilding those compositions locally.

Child order may change when dependency evidence suggests a better route, but
all concrete structures must preserve the configured `picorv32.v` signal and
state ownership described in [docs/PicoRV32Plan.md](docs/PicoRV32Plan.md).

### Continue reducing contract-boundary proof boilerplate

The schedule derivation and child-contract fact tactics substantially shortened
module certification while leaving each meaningful rule order and behavioral
argument visible. They are established inputs to the authoring-surface work
above rather than a separate reason to add isolated helpers.

The first follow-up now provides child-contract fact extraction inside an
`implements` proof. Given the structural-solution hypothesis, the generic
helpers:

1. obtain a selected child's evaluation from its public certification;
2. apply a selected public theorem about that child's contract; and
3. normalize the child inputs induced by the parent's wiring.

The implementation was validated on `HalfAdder` and `FullAdder`, then on the
ALU's equality and bitwise child facts. It removes the manual stateless-child
setup and the repeated wiring-normalization lists while preserving named,
fully typed intermediate equations. It uses only child certifications and
public contract theorems, never hidden child structures. Focused HalfAdder and
FullAdder checks remain under two seconds. The ALU remains around eight
seconds, so this improvement should not be treated as a solution to its
separate elaboration-performance problem.

Two narrower repeated patterns may justify support as part of the API and
certification stages above:

- assembling a parent's state-correspondence existence proof from the
  corresponding states of its named or indexed children; and
- handling empty-state children without repeatedly introducing a
  `Subsingleton` instance and proving equality with `SignalMap.emptyValues`.

Do not hide module bodies, wiring, module-specific Boolean or arithmetic
reasoning, or the final behavioral argument merely to reduce line count. The
authoring syntax may make bodies and wiring more concise, but those parts still
describe the hardware and must remain readable in the module file.

### Define and prove processor-level observation

Before claiming CPU correctness:

1. define the external memory environment and identify the memory-mapped-I/O
   address region outside the processor core;
2. define observable completed bus transactions, trap, and termination;
3. adapt the Sail-derived RV32I transition model in the sibling
   `sail-riscv32-lean` work into an instruction-retirement trace;
4. prove that the source-faithful microarchitectural execution refines that
   architectural trace; and
5. derive the weak public theorem about I/O traces, with ordinary-memory
   correspondence as a stronger supporting property where required.

This verification must not introduce RVFI hardware into the emitted design.
Any retirement record is a proof-level observation reconstructed from existing
state and bus behavior.

## Longer-term work

- Prove a semantics-preservation bridge from the supported closed
  `ModuleStructure` subset to emitted FIRRTL, or validate a smaller checked
  backend representation if that gives a clearer theorem.
- Add contract forms for other useful temporal abstractions as real designs
  demand them.
- Explore whether memory arrays deserve a structural primitive only when a
  design requires one; current plans do not assume it.
- Evaluate proof and elaboration performance as CPU structures replace
  blackboxes, keeping focused builds comfortably interactive.

## Completion standards

A feature is complete only when its public structure and natural contract are
clear, the relevant existence or non-vacuity condition is proved, reusable
proofs do not depend on hidden child implementations, documentation states the
actual correctness boundary, and the appropriate Lean and generated-hardware
regressions pass.
