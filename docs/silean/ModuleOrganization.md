# Module development and file organization

This guide describes how to add a reusable hardware module to Silean. It is a
default, not a requirement to manufacture empty files or force every behavior
into the same contract type.

The guiding rule is simple: a reader should be able to understand the module's
boundary and promised behavior without reading its wiring or proof machinery.

## Development order

Develop a module in this order:

1. Define the boundary and state the intended behavior in natural Lean.
2. Choose the contract form that expresses that behavior directly.
3. Build the hardware structure.
4. Prove structural existence and uniqueness.
5. Prove that the structure satisfies the contract.
6. Expose only the results a parent module should use.

The contract comes before the proof and should not be changed merely to make a
particular implementation easier to verify. If the proof becomes awkward,
first ask whether the structure, contract boundary, or reusable framework API
is wrong or incomplete.

## Start with a natural boundary and contract

Use `module_ports` for a normal boundary:

```lean
module_ports ports (width : Nat) where
  input left : .vector width .bit,
  input right : .vector width .bit,
  output result : .vector width .bit
```

It generates the typed label maps, `ModulePorts`, boundary naming, and helpers
used by placement and authoring. Use `signal_schema` when a named aggregate
shape and its typed field accessors will be reused in several places.

The contract should say what the module means, not how its children happen to
compute it. Prefer:

- ordinary Boolean, natural, integer, rational, complex, list, or vector
  functions;
- explicit encoding and decoding at the hardware boundary;
- explicit wrapping, rounding, saturation, ordering, latency, framing, and
  protocol assumptions when observable; and
- abstract behavioral state rather than a copy of the register hierarchy.

Do not define a multiplier contract as a tree of partial-product and adder
operations, or a partial-product row as a mask followed by a layout. State the
numeric result and encode it at the declared width. The implementation proof is
where the structural decomposition belongs.

A useful review test is: if a different hierarchy computed the same external
result, would the contract stay unchanged? It usually should.

## Choose the right contract shape

There is no mandatory universal module contract.

### Exact cycle behavior

Use `ModuleCycleContract` when named output rules and one next-state function
are the natural one-cycle interface. `module_cycle_contract` generates the rule
names, typed selections, equations, coverage proof, and assembled contract:

```lean
module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule result where
    reads := [left, right]
    writes := { result := resultValue left right }
  state_rule where
    reads := []
    next := {}
```

Use the generated projections such as `cycleContract.result allowed` directly.
Do not add aliases like `result_of_allowed` unless they state a genuinely more
natural or derived fact.

### Fixed-latency and framed behavior

For a pipeline whose useful meaning is “apply this function or relation after
`L` cycles,” use a state-free `BoundaryTrace` and `FixedLatency`. Do not expose
physical registers as contract state merely to express delay.

For a complete marker-delimited window of samples, use `FramedLatency`. State
the frame length, marker rule, latency, and relation on complete frames. If an
early marker invalidates an interrupted candidate frame, put that condition in
the contract antecedent rather than inventing reset or initialization state.

Compose these contracts with their serial, parallel, and input/output mapping
laws rather than re-proving cycle-index arithmetic in each parent.

### Custom relations

Some modules are naturally relational. A carry-save tree, for example, should
promise preservation of the represented sum without choosing one canonical
pair of output operands. Such a module can use an ordinary predicate and prove
it directly for every realized structural step.

A custom behavioral relation still needs an independent structural proof that
the hardware equations have exactly one solution. Do not invent a
deterministic cycle contract solely to obtain that proof.

## Build one authoritative structure

`module_design` is the normal way to write a fixed composite. It declares the
immediate children and total typed wiring, and generates the permanent
`ModuleBody`. When every child is concrete it also generates the
`ModuleStructure`, recursive naming, and named design:

```lean
module_design Foo where
  boundary (Foo.ports width) (naming := Foo.Naming.ports width)
  instances {
    first := ChildA.design width,
    second := ChildB.design width }
  wiring {
    outputs {
      .result := second.result }
    instance (.first) {
      .input := input.left }
    instance (.second) {
      .input := first.result }
  }
```

The exact labels depend on the module, but the source should make the hardware
topology obvious. Use named wires only when a name materially helps explain or
debug an intermediate value.

Recursive structures, indexed child families, and generated networks may be
clearer as ordinary Lean definitions. That is not a second API: they construct
the same `ModuleBody` and `ModuleStructure` values. Prefer the representation
that makes the topology easiest to review.

The optional `CircuitDescription.ModuleBuilder` notation used by some existing
modules is a separate human-facing presentation connected to the production
structure by a correspondence proof. Do not add it by default. Retain or add
one only when it explains a circuit substantially better than its
`module_design` or recursive structural definition.

## Top-down work with unresolved children

When the parent boundary and wiring are known before a child implementation,
write that child as `unresolved (ports)` in `module_design`. The command still
generates its child interface, wiring, and `ModuleBody`, but deliberately does
not invent state or executable semantics.

State a conditional parent theorem over a `ModuleBody.Trace`:

- assume `trace.WiringHolds`;
- assume the required predicate for each `trace.child childName`; and
- prove the desired predicate for `trace.parent`.

Those predicates may be cycle, fixed-latency, framed, or completely custom.
Once the children are concrete, the generic observation bridge obtains the
same synchronized body trace from composite execution. Resolving the outline
should require changing only each child right-hand side; the boundary, wiring,
body, and conditional proof remain useful.

## Standard file layout

A nontrivial reusable module normally uses:

```text
Foo/
|- Foo.lean
|- FooDerived.lean
`- Internal/
   |- FooStructure.lean
   `- FooVerification.lean
```

Add a separate internal correspondence or arithmetic file only when it names a
real proof responsibility. Small leaves may keep everything in one file.

### `Foo.lean`: public meaning

The main file contains, as applicable:

- a short statement of purpose;
- the `module_ports` boundary;
- natural pure functions or relations defining behavior;
- the selected behavioral contract; and
- short consequences that explain or simplify that contract.

It must not import its own `Internal/` directory. It should not contain child
certification maps, proof schedules, expanded recursive wiring, or long tactic
proofs.

### `Internal/FooStructure.lean`: hardware

The structure file contains the authoritative `module_design` or ordinary Lean
construction, including:

- immediate child structures;
- complete typed wiring;
- the resulting `ModuleBody` and `ModuleStructure`;
- recursive naming and `NamedModule` values; and
- structure-specific helpers that are not behavioral API.

For a top-down module, its body may intentionally be public before this file is
fully concrete. For a compact module whose structure is itself the clearest
part of its public story, combining the main and structure files is fine.

### `Internal/FooVerification.lean`: proof construction

The verification file owns schedules, state correspondence, structural
existence and uniqueness, child-interface reasoning, and the detailed proof of
the public behavioral result. Proof-local helpers should be `private`; helpers
that must cross an internal file boundary should live under `Foo.Internal`.

### `FooDerived.lean`: public results backed by internals

The derived facade imports verification and exposes only stable results, such
as:

- placement helpers and the concrete design;
- a cycle certification needed when the module is a child;
- `structuralCertification` for a module using another contract style;
- a theorem that every realization or execution satisfies the public contract;
  and
- genuinely useful semantic consequences.

The theorem statement should use declarations from `Foo.lean` wherever
possible. It must not expose raw wiring, generated child-label types, schedules,
or structural state correspondence.

## Prove structure and behavior separately

Every concrete hierarchy needs existence and uniqueness independently of its
behavioral contract. `ModuleStructuralRules` state which boundary inputs a rule
reads and which outputs it determines. A checked complete schedule over
certified children yields a `ModuleStructuralCertification`.

For an exact cycle contract:

1. associate each child with its public certification;
2. use `module_rule_schedules` to declare the dependency-correct child rule
   calls for each parent output and next state;
3. define the relation between behavioral and structural state; and
4. use `module_cycle_certification` to package structural and behavioral
   correctness.

For another contract style, use `module_complete_schedule` to prove
contract-independent structural solvability, then prove the behavioral trace
or relation directly. Every structurally certified child automatically has a
safe whole-module dependency rule; add finer rules only when composition needs
them.

Parent proofs must use public child interfaces. For cycle-certified children,
retain the returned `ChildContractMatch` and use its rule, boundary-equation,
aggregate-fact, and next-state projections. For trace contracts, observe the
whole execution once and project synchronized child executions from that same
observation. Do not unfold child gates, register trees, or private invariants.

## Public and internal boundaries

`Internal/` is an organizational convention, not a Lean access modifier. Keep
the boundary effective in three ways:

1. Code outside `Foo/` imports only `Foo.lean` or `FooDerived.lean`.
2. Cross-file implementation helpers use the `Foo.Internal` namespace.
3. Same-file proof helpers are declared `private`.

Generated declarations require the same judgment as handwritten ones. A macro
helper is not public merely because the macro can generate it. Conversely,
`moduleStructure`, naming, design, certification, and a body deliberately used
for top-down composition may be supported public artifacts even if physically
defined under `Internal/`.

Do not preserve obsolete APIs with compatibility wrappers. Mark a temporary
compatibility declaration deprecated, migrate its users, and remove it with
the last user so two permanent ways of doing the same thing do not emerge.

## Naming and emission

Port and child labels are semantic structural identities. Reader-facing names
are emission metadata.

Let `module_ports` and `module_design` generate ordinary naming whenever
possible. Handwritten recursive naming may use `ModuleNaming.withPorts` to
replace only external port metadata while retaining its module key, child
names, recursive naming, and named wires. Do not add projection theorems such
as `naming_ports` speculatively; add one only for a real consumer.

A value-specialized module such as a ROM may require a caller-supplied
definition name. That identifies a reusable emitted definition, not a placed
instance. Reusing the same definition key for a different rendered body must
remain an emitter error.

FIRRTL is emitted from the concrete named `ModuleStructure`, never from a
contract, proof schedule, or optional builder description.

## Review checklist

Before treating a module as complete, check that:

- its contract is natural Lean and states every observable width, ordering,
  rounding, latency, reset, and protocol detail;
- it has one authoritative hardware structure;
- its simultaneous equations have proved existence and uniqueness;
- its behavioral theorem is non-vacuous and uses only public child facts;
- public theorem statements do not expose proof machinery;
- naming metadata is separate from structural identity;
- focused Lean tests import the same public facade expected of downstream code;
- generated-hardware tests are added when emission behavior matters; and
- production proofs contain no `sorry`, project axioms, `native_decide`, or
  unsafe shortcuts.

Tests and illustrative executable checks may use evaluation mechanisms that
are inappropriate in production proofs. Test fixtures belong under `tests/`,
not in reader-facing module files.
