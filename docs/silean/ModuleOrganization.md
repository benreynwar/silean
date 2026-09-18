# Module file organization

This document describes the intended source layout for a reusable hardware
module. The layout has two purposes:

1. a reader should be able to understand what the module is and what has been
   proved about it without reading proof machinery; and
2. downstream Lean code should have a clear, stable interface that does not
   depend on the module's wiring or certification internals.

The organization is a default, not a reason to create empty files. A primitive
or very small leaf may need only its main file. A module with several genuinely
different contracts may need additional files named after those contracts.

## Standard directory

An ordinary composite module should normally have this shape:

```text
Silean/Modules/Foo/
|- Foo.lean
|- FooTheorems.lean
`- Internal/
   |- FooStructure.lean
   `- FooVerification.lean
```

The intended reading order is `Foo.lean`, followed by `FooTheorems.lean`.
Someone trying to understand the certified result should not need to read the
files under `Internal/`. Those files remain available to someone maintaining
or debugging the elaboration and proof.

## Authoring interface

An ordinary fixed module should be written first with
`Authoring.CircuitDescription.Builder`. This is the human-facing hardware
definition: its `do` notation, named inputs and outputs, placed children,
wires, and assignments should resemble the structure a Verilog author expects
to see.

For example, the main definition should have the general shape:

```lean
noncomputable def construction : Builder Unit := do
  let left <- input "left" .bit
  let right <- input "right" .bit
  let result <- SomeChild.place left right
  output "result" result

noncomputable def description : Description :=
  build construction
```

Authors should use documented placement helpers such as `place` or
`placeNamed` rather than manually assembling a child's description. Placement
helpers retain the child's production `design`, including its structure and
naming, and give parent descriptions a compact hardware-oriented vocabulary.

The builder description is not a second semantics and is not used directly by
certification or FIRRTL emission. The production representation remains the
fully typed `module_design` declaration in `Internal/FooStructure.lean`. It
provides the total wiring, `ModuleStructure`, naming, and `NamedModule` values
consumed by the rest of Silean.

Every module using this two-representation pattern must expose an
`authored_definition_corresponds` theorem in `FooTheorems.lean`. That theorem
checks that finalizing the readable builder description produces exactly the
named production structure, including its boundary, children, connections,
and uniqueness of names. The detailed correspondence proof belongs in
`Internal/FooVerification.lean`.

The two declarations must not be allowed to drift:

- the builder description is what a person reads to understand the hardware;
- the typed structure is what verification and emission consume; and
- `authored_definition_corresponds` is the checked connection between them.

`module_design` may remain the primary authoring form when the builder would
hide rather than clarify the construction. Typical exceptions are recursive
module families, indexed or programmatically generated hierarchies, and
generic composition mechanisms. The main file should briefly explain such an
exception. Avoid introducing a builder description merely to reproduce a
large generated structure less clearly.

## `Foo.lean`: definition and contract

The main file explains what the hardware is. It should contain, as applicable:

- a module-level description of the circuit and its purpose;
- the concise, hardware-oriented authored definition;
- small placement helpers intended for authors of parent circuits;
- named functions or propositions that express the module's natural behavior;
- the exact cycle contract; and
- short, fundamental conversions that explain the meaning of that contract.

The authored definition should be the form a hardware author is expected to
read and write. The contract should state the behavior independently of the
implementation hierarchy. A reader should be able to see the ports, important
children or operations, output behavior, and state transition from this file.

This file may import `Internal/FooStructure.lean` to obtain the expanded typed
structure generated from the authored form. It should not contain child
certification maps, schedules, structural-solution proofs, or long tactic
proofs.

Downstream circuit-authoring code normally imports this file and uses:

- `Input`, `Output`, and `ports` for the boundary;
- `place` or another documented placement helper when one exists;
- `design` or `designWith` when declaring a child in `module_design`;
- `moduleStructure` and `naming` for lower-level structural consumers; and
- the behavior and cycle-contract declarations when stating specifications.

## `FooTheorems.lean`: public guarantees

The theorem file states what downstream proofs may rely on. It should contain:

- useful consequences of the contract, stated at the module's natural level;
- the theorem connecting the authored definition to the production structure;
- the main theorem that the structure implements its contract; and
- additional semantic results that are useful to proofs using the module.

These should be real reusable theorem interfaces, not duplicate propositions
created only to make the file look explanatory. Comments should explain the
roles of unfamiliar arguments and why a theorem is useful to a parent proof.

Proofs in this file should normally be short. They may delegate to lemmas or a
certification constructed in `Internal/FooVerification.lean`, but their
statements must not expose schedules, intermediate child proposals, or other
proof-specific choices unless those concepts are inherently part of the
module's public semantics.

Public one-cycle theorems should use the shared boundary-step vocabulary:

- a contract theorem takes `step : cycleContract.Step` and a proof of
  `cycleContract.Allows step`; and
- a structural theorem takes `step : moduleStructure.Step` and a proof of
  `moduleStructure.Realizes step`.

This keeps `inputs`, `currentState`, `outputs`, and `nextState` together and
prevents structural witnesses from leaking into the public interface.
`IsSolution` and `HierStep` remain internal structural witnesses used to
establish `Realizes`. The superseded four-argument `EvaluatesTo` relation and
its compatibility layer have been removed; use `Allows`. A combinational
module may still expose a smaller
`Behavior step.inputs step.outputs` proposition; the theorem deriving that
behavior should accept `Allows step` or `Realizes step`.

When proving a parent module from its children, keep the returned
`ChildContractMatch` intact. Use `childMatch.ruleHolds rule` for one declared
output rule, `childMatch.boundaryFact theorem` for a public theorem that turns
an allowed step into an input/output property, and
`childMatch.nextCorresponds` for state threading. `childContractStep` is
layer-certification machinery and should not appear in module proofs.

Downstream verification code normally imports this file. In addition to its
named theorems, it may use:

- `certification`, when the module is a certified child of another module; and
- `certified`, when the complete packaged certified module is required; and
- `certifiedLayer`, when deliberately reusing the module body with a different
  family of children satisfying the same child contracts.

Importing `FooTheorems.lean` also makes the definitions from `Foo.lean`
available, so downstream code should not separately import both.

## `Internal/FooStructure.lean`: expanded typed hardware

The structure file contains the mechanically explicit representation used by
the framework. It normally contains:

- `module_ports` when the boundary is generated there;
- the expanded `module_design` declaration;
- child-instance types and boundaries;
- total typed wiring;
- the resulting `ModuleBody` and `ModuleStructure`; and
- structural naming and `NamedModule` bundles.

This file exists because the explicit typed structure is useful to Lean,
emission, and verification but is usually noisier than the authored circuit.
It contains no behavioral correctness proof.

Some declarations generated in this file are deliberate public artifacts:
`ports`, `moduleStructure`, `naming`, `namingWith`, `design`, and `designWith`,
along with their boundary label types. Their physical location under
`Internal/` keeps the normal reading path clean; it does not make those
particular declarations unsupported.

Other generated declarations, such as raw contexts, child maps, wiring, and
module bodies, are structural implementation details. Downstream code should
not use them merely because Lean makes them visible through a transitive
import.

## `Internal/FooVerification.lean`: proof construction

The verification file contains the details needed to build the public
certificate. It normally contains:

- certified-child selection;
- output and state proof schedules;
- the relation between contract state and structural state;
- existence, uniqueness, and contract-implementation arguments;
- detailed authored-description correspondence proofs; and
- construction of `certification` and `certified`.

Proof-local declarations should be `private` whenever they are used only in
this file. A supporting declaration that must cross a Lean file boundary but
is not a supported API should live under `Foo.Internal`, so its name clearly
marks that status.

`certification` and `certified` are exceptions: although constructed in the
verification file, they are intentional public results. The former is the
compositional interface used when `Foo` is a child; the latter packages the
structure, contract, and certificate for general consumption.

## The public boundary

An `Internal/` directory is an organizational convention, not a Lean access
modifier. Imports are transitive, and a declaration in an internal file is
still accessible unless it is declared `private`. Moreover, Lean's `private`
declarations cannot be referenced from a different source file.

The project therefore uses three reinforcing boundaries:

1. **Import boundary.** Code outside `Foo/` imports only `Foo.lean` or
   `FooTheorems.lean`, never a path under `Foo/Internal/`.
2. **Namespace boundary.** Non-public declarations that must cross files use
   the `Foo.Internal` namespace.
3. **Language boundary.** Declarations used within one file are marked
   `private` whenever possible.

The supported downstream interface for an ordinary module is:

- its boundary labels and `ports`;
- its documented placement and design values;
- `moduleStructure` and naming values needed by structural tools;
- its behavior and contract, including named rules required for composition;
- its `Step`-based `Allows` and `Realizes` theorem interfaces;
- the theorems in `FooTheorems.lean`; and
- its `certification`, `certified`, and deliberately reusable
  `certifiedLayer` values.

Raw wiring, bodies, contexts, concrete child maps, schedules,
state-representation relations, and intermediate proof lemmas are not part of
that interface unless the module explicitly documents an exception.

Do not add compatibility wrappers for superseded cycle representations. Migrate
callers to the shared `Step` interface and remove the old declaration with its
last consumer.

Generated declarations need the same audit as handwritten ones. A macro
helper should be generated as `private` or under `Internal` when consumers do
not need it; generation by a macro is not itself a reason to expose it.

## Imports and aggregate exports

Use the narrowest public import that provides the required layer:

```lean
-- Defining or composing hardware:
import Silean.Modules.Foo.Foo

-- Proving properties or certifying a parent:
import Silean.Modules.Foo.FooTheorems
```

`Silean.Modules` should import the theorem file for an ordinary fully certified
module, making the complete supported interface available from the aggregate.
Internal files must not be imported by unrelated modules as a shortcut around
the public façade.

The only ordinary main files that import a path under their own `Internal/`
directory are the owners of an expanded structure generated there. Code
outside that module imports the main file or theorem façade instead.

## Variations

The four-file layout should be adapted when the module's semantics require it:

- A primitive or simple leaf may keep its definition, contract, and short
  proof together when splitting them would make navigation worse.
- A module refined through several abstraction levels may have a separate
  public file for each independently useful contract, such as exact-cycle and
  FIFO behavior.
- A large proof may use several files under `Internal/`, named for their proof
  responsibilities rather than numbered as arbitrary chunks.
- A private child meaningful only as part of its parent may live in a
  subdirectory of that parent instead of becoming a top-level reusable module.
- Recursive or programmatically generated families may expose a different
  construction surface, but should preserve the same distinction between
  definition, public guarantees, and proof machinery.
- A generic composition mechanism parameterized by arbitrary certified
  children may live under `Composition/` rather than imitate a concrete module
  directory. Its public certification constructor should be named for that
  role, while its schedules and proof-local helpers remain private.

The register-to-FIFO stack supplies concrete examples of each variation:

- `Register` keeps its type-directed recursive construction in
  `Register.lean`, because that recursion is the clearest hardware definition.
  `Internal/RegisterVerification.lean` contains the recursive certification,
  while `RegisterTheorems.lean` is the public proof interface.
- `Equality`, `BinaryToOneHot`, and `CombMuxTree` follow the same split for
  recursive combinational hardware: the main file shows the recursive
  structure, `Internal/*Verification.lean` contains schedules and inductive
  certification, and `*Theorems.lean` states the supported structural result.
- `Add` and `Increment` use that split for recursive ripple hardware;
  `AddSub` uses it for an authored fixed composite. Their main files own the
  natural arithmetic behavior, while theorem files are the downstream proof
  boundary.
- `SerialDepthFifo` keeps recursive composition as its hardware definition,
  while recursive certification is under `Internal/` and public cycle/FIFO
  results are separate theorem files.
- `OneEntryFifoCycleTheorems.lean` and
  `OneEntryFifoFifoTheorems.lean` distinguish exact clock behavior from the
  capacity-one abstract queue guarantee.
- `OneEntryFifo/Control/` is organized as a private child beneath the only
  parent for which its handshake decisions are meaningful.

Additional files should correspond to concepts a reader or maintainer can
name. They should not split a linear proof merely to reduce file length.

## Checks and examples

Compilation examples and regression checks belong under
`tests/silean/lean/SileanTests/`, not in the module's reader-facing files. They should
import the same public façade expected of downstream users. This checks both
the declarations and the intended import boundary.

The main and theorem files may still contain small checked `example`
declarations when those examples materially teach a type or authoring form.
Such examples should be unmistakably illustrative and must not be dependencies
of production code.
