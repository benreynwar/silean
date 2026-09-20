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

## Development order

Develop a module in this order:

1. define its boundary, natural Lean semantics, and cycle contract;
2. build the hardware structure that is intended to realize that contract; and
3. prove correspondence, certification, and any derived mathematical results.

The contract is the specification, so it should be readable and settled before
the implementation and proof machinery begin to shape the module. In
particular, write the contract in the most natural Lean terms for users of the
module, rather than describing the implementation's wires, child instances, or
intermediate signals. The hardware may introduce those details afterward, and
the proof is the bridge between the two.

This order is also the intended reading order within a main module file: put the
semantics and contract before an authored construction when both live in that
file. Internal structure and verification files follow the same conceptual
order even when Lean import dependencies require them to be separate files.

## Standard directory

An ordinary composite module should normally have this shape:

```text
Silean/Modules/Foo/
|- Foo.lean
|- FooDerived.lean
`- Internal/
   |- FooStructure.lean
   |- FooCorrespondence.lean  (when useful as a separate check)
   `- FooVerification.lean
```

The intended reading order is `Foo.lean`, followed by `FooDerived.lean`.
Someone trying to understand the certified result should not need to read the
files under `Internal/`. Those files remain available to someone maintaining
or debugging the elaboration and proof.

`Derived` means “public declarations whose definitions or proofs require the
generated internals.” It does not mean that the file owns another hardware
representation. Placement helpers, the concrete `design`, and short public
theorems backed by internal proofs naturally live at this boundary.

For an authored module, the public signatures in `FooDerived.lean` must use
only declarations available from `Foo.lean` and the public authoring API. The
implementation of `Foo.place` may consume the generated structure and naming,
and a theorem proof may name an internal theorem. Neither dependency should
appear in the placement type or theorem statement. The contract-first
structural pattern below makes one explicit exception for its concrete
structure-correctness statement.

HalfAdder is the reference instance of this layout:

```text
HalfAdder.lean
    ^
    | imported by
Internal/HalfAdderStructure.lean
    ^
    | imported by
Internal/HalfAdderVerification.lean
    ^
    | imported by
HalfAdderDerived.lean
```

`HalfAdder.lean` declares the ports once, then contains the readable XOR/AND
construction, exact cycle contract, and its arithmetic meaning. The generated
structure reuses that boundary rather than declaring it again. Internal
verification proves concrete correspondence and certification, then proves the
implementation-independent claim by transporting structural solutions through
`Corresponds`. `HalfAdderDerived.lean` exposes `place` and a one-line
`construction_correct` theorem whose proof simply names the internal result.

HalfAdder also supplies two useful mechanical checks for this organization:

- the import closure of `HalfAdder.lean` contains neither its own generated
  structure nor verification module; and
- if the proof of a public theorem in `HalfAdderDerived.lean` is replaced by
  `by sorry`, its statement elaborates using `HalfAdder.lean` alone.

The register family is the reference for the same organization with state:

```text
Register.lean / ResetRegister.lean / EnabledRegister.lean /
EnabledResetRegister.lean / EnabledResetCounter.lean
    boundary, readable construction when useful, state model, cycle contract,
    and direct consequences of that contract

Internal/*Structure.lean
    expanded recursive or composite hierarchy and naming

Internal/*Verification.lean
    state correspondence, schedules, authored-description correspondence,
    and certification

*Derived.lean
    placement and the public correctness proof backed by those internals
```

For a stateful authored module, the main file should make two times explicit:
outputs describe the stored value before the edge, while the state rule
describes the stored value after the edge. Use the output projections generated
by `module_cycle_contract` for the first fact. Short `*_of_allowed` theorems may
spell out state transitions or genuinely derived consequences beside the
contract in the main file. They depend only on `cycleContract.Allows`; they are
not certification results and must not be hidden behind an internal import.

Feedback wires belong in the readable construction when they explain the
hardware. Their matching `named_wires` entries and the relation between the
contract state and nested child state belong under `Internal/`. The public
`construction_correct` theorem in the derived file connects any realization
of the readable construction to the contract without exposing that state
relation in its statement.

## Contract-first structural modules

Some hardware is most naturally implemented by recursive Lean definitions,
indexed families, or another programmatic structural construction. If a
`ModuleBuilder` description would obscure that implementation or duplicate it
poorly, do not force one into the module. Equally, do not put the expanded
structural construction in `Foo.lean` merely because no concise authored form
exists.

Use the same directory shape with a different correctness boundary:

```text
Foo.lean                         boundary, behavior, and cycle contract
FooDerived.lean                  placement and public structural correctness
Internal/FooStructure.lean       recursive or programmatic implementation
Internal/FooVerification.lean    certification proof
```

`Foo.lean` should remain the file a human reads to understand what the module
does. It declares the ports, mathematical behavior, exact cycle contract, and
short contract-level consequences. It contains no `Description`, correspondence
proof, child hierarchy, recursive wiring, structural naming, or placement
implementation unless one of those is itself genuinely simple and explanatory.

Because this pattern has no independent authored description, its derived
correctness theorem names the generated structure directly:

```lean
theorem implements_contract (parameter : Parameter) :
    Contracts.Cycle.Implements (moduleStructure parameter)
      (cycleContract parameter)
      (certification parameter).stateCorresponds :=
  (certification parameter).implements
```

This theorem is intentionally different from an authored module's
`description.ImplementsCycleContract`: the concrete `moduleStructure` and its
state correspondence are part of the claim. They are generated under
`Internal/` but exposed through `FooDerived.lean` as deliberate structural
artifacts. Raw child labels, wiring tables, schedules, and proof helpers remain
internal.

Do not invent a builder description solely to obtain the authored-module
theorem shape. The two supported patterns are “readable authored construction
plus correspondence” and “small public contract plus directly certified
internal structure.” In both patterns, `Foo.lean` stays simple.

`Add` and `Increment` are reference examples of the contract-first structural
pattern. `CarrySaveAdder` is the reference for an indexed family of children:
its `module_design` is the sole hardware representation rather than being
duplicated as a recursive builder description. `AddSub` is the corresponding
arithmetic example with a concise authored construction and an
implementation-independent correctness theorem.

## Authoring interface

An ordinary fixed module with a concise authored implementation should declare
its boundary with `module_ports`, then write its construction with
`Authoring.CircuitDescription.ModuleBuilder`. This is the human-facing hardware
definition: its `do` notation, typed inputs and outputs, placed children, wires,
and assignments should resemble the structure a Verilog author expects to see.
The generated boundary operations live in the namespace named by the
`module_ports` declaration; opening that namespace gives the construction the
short `input` and `output` spellings.

For example, the main definition should have the general shape:

```lean
module_ports ports where
  input left : .bit,
  input right : .bit,
  output result : .bit

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let left <- input .left
  let right <- input .right
  let result <- SomeChild.place left right
  output .result result

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction
```

The boundary supplies each port's name and signal type, so the construction
does not repeat either one. It also supplies the complete input list when the
description is built: referring to an input reads that declared port rather
than declaring it again. Ordinary `Builder` actions lift into `ModuleBuilder`,
so placement, wires, registers, and logic operators keep their existing APIs.

When a canonical boundary is already owned by an interface module, reuse it
instead of declaring the same ports again. Put reusable typed authoring
adapters beside the authoring layer, following the generated `ports.input`,
`ports.output`, `ports.OutputNets`, and placement shape. The FIFO family uses
`Authoring/FifoPorts.lean` this way. A one-off construction can use
`ModuleBuilder.input (ports := ...)` and `ModuleBuilder.output` directly, but
should never duplicate an established interface merely to obtain shorter
operations.

Authors should use a child's documented `place` helper rather than manually
assembling its description. Placement helpers retain the child's production
`design`, including its structure and naming, and give parent descriptions a
compact hardware-oriented vocabulary. `placeNamed` is an explicit opt-in for
the uncommon case where a caller-chosen instance name is useful; it is not the
default spelling.

`module_ports` generates `ports.OutputNets` together with boundary-specific
`ports.placeNamed` and `ports.placeIndexed` adapters. A module's public
placement wrapper should use those declarations instead of repeating the
output ports in a handwritten `PlacedOutputs` structure, matching every input
label by hand, and repackaging every output. For example:

```lean
noncomputable def place (left right : Net .bit) : Builder ports.OutputNets :=
  ports.placeIndexed "half_adder" moduleStructure naming left right
```

Introduce a separate placement-result type only when it expresses a real
abstraction not already present in the declared output boundary. Do not retain
an abbreviation such as `PlacedOutputs := ports.OutputNets` merely to preserve
an otherwise unused name.

Every reusable module should keep `Foo.place` as its explicit, dependable
placement API. A common expression-like module may additionally expose a short
name directly in `Silean.Authoring`, such as `halfAdder` or `constant`. For a
single module, define that abbreviation physically in `FooDerived.lean`: this
keeps its dependency on the concrete placement API local without adding a tiny
coordination file. An operation that dispatches among several modules, such as
`mux` or the arithmetic operators, belongs in a shared authoring file instead.
The source-file boundary organizes dependencies; it need not introduce another
public namespace.

Ordinary vocabulary is enabled with `open Silean.Authoring`. Operators remain
scoped so merely importing an authoring dependency does not silently change the
parser; an authored module opts into them with `open scoped Silean.Authoring`.
Less common placements should continue to use `Foo.place`.

The authored definition should use the project’s hardware notation when it is
available. In particular, prefer `!!`, `&&&`, `^^^`, `|||`, and `===` to
spelling out primitive or recursive logic placement. These operators return
builder actions, so a result used only once should normally be embedded with a
nested `←` instead of receiving a temporary name:

```lean
output .result (← (left &&& (← !! select)) ||| (right &&& select))
```

For a named aggregate declared with `signal_schema`, use its generated
`layout` when exposing fields. The ordinary form uses a conventional indexed
splitter name; use `splitNamed` only when the structural instance name itself
is meaningful:

```lean
let inputsFields ← split ControlInputs.layout inputs
let currentFields ← split ControlState.layout current
```

The ordinary forms of structural operations do not accept instance names:
use `split`, `splitVector`, `combine`, `update`, `mux`, and `register` with
their data arguments. They choose conventional indexed names. Their
`splitNamed`, `splitVectorNamed`, `combineNamed`, `updateNamed`, `muxNamed`,
and `registerNamed` counterparts exist only for the uncommon case where an
explicit structural name is clearly useful. In particular, do not preserve an
incidental name merely because it appeared in an older expanded declaration.

`mux select whenFalse whenTrue` chooses the bit-specific or aggregate mux from
its result type automatically.

Use `let` when a result fans out to multiple consumers or when its name is a
meaningful part of explaining the circuit. Do not introduce a sequence of
one-use `let` bindings merely to mirror the expanded child list.

When such a meaningful intermediate should also be recognizable in generated
FIRRTL and debugging waveforms, declare it as a `wire`:

```lean
wire addressesEqual ← readAddress === writeAddress
let inputReady ← !! (← addressesEqual &&& full)
```

An immediately driven wire may state its signal type explicitly when that is
helpful: `wire addressesEqual : .bit ← ...`. A forward-declared wire uses
`wire result : .bit` and receives its driver later through `assign`. In every
form, the wire's spelling is retained as emission metadata. It does not add a
structural endpoint or equation. Use wires when the name helps explain or
debug the circuit. Boundary ports are already named and should not be repeated
as wires.

Likewise, `Foo.place` is the default for placing a module. Use
`Foo.placeNamed` only when the chosen instance name carries information that
the child module and its position do not already provide, or when it is an
intentional stable debugging name. For example, names can usefully distinguish
two instances of the same counter as `readCounter` and `writeCounter`; naming a
sole `Lookahead` child `lookahead` adds no information. During migration, an
incidental name from the old expanded declaration is not by itself a reason to
use `placeNamed` and make the reader-facing circuit verbose. The expanded
`module_design` should follow the authored definition's placement order and
names. A reader-facing `wire` is mirrored there with a `named_wires` section
identifying the same typed structural source:

```lean
named_wires {
  addressesEqual := addressEquality.result }
```

This metadata participates in authored-definition correspondence checking and
FIRRTL name validation, while `wiring` remains the complete structural
circuit. The project Makefile passes `--preserve-values=named` to firtool so
these names survive into generated SystemVerilog; direct firtool invocations
must do the same. Aggregate wires are flattened during lowering but retain the
authored name as their common prefix. When an existing name really must remain
stable, make that exception explicit rather than obscuring every logic
expression with manual naming.

The builder description is not a second semantics and is not used directly by
certification or FIRRTL emission. The production representation remains the
fully typed `module_design` declaration in `Internal/FooStructure.lean`. It
provides the total wiring, `ModuleStructure`, naming, and `NamedModule` values
consumed by the rest of Silean.

Every module using this two-representation pattern should expose a public
`construction_correct` theorem in `FooDerived.lean`. Its statement quantifies
over every typed realization whose naming `Corresponds` to the authored
description, so it mentions neither generated label constructors nor one
chosen structure. The generated correspondence certificate and detailed proof
belong in `Internal/FooVerification.lean`.

The two declarations must not be allowed to drift:

- the builder description is what a person reads to understand the hardware;
- the typed structure is what verification and emission consume; and
- the internal `Corresponds` certificate connects them, while public
  `construction_correct` states that every such realization meets the contract.

### Boundary naming convention

The `module_ports` declaration owns a module's authoritative boundary naming.
An ordinary `module_design` must reuse that naming in its `boundary` clause;
the generated hierarchical naming should therefore project back to exactly the
declared boundary naming.

Handwritten recursive structures need a little more care. When a recursive
naming definition does not directly expose the caller-supplied
`SignalTypeNaming` at its boundary, keep recursive hierarchy construction in a
private core and normalize the public boundary with `ModuleNaming.withPorts`:

```lean
private def namingCore ...
    (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (moduleStructure ...) :=
  -- Name recursive children and internal adapters, propagating typeNaming
  -- wherever their emitted aggregate names should remain meaningful.
  ...

def namingWith ... (typeNaming : SignalTypeNaming signalType) :=
  (namingCore ... typeNaming).withPorts
    (Naming.portsWithNaming ... typeNaming)

def naming ... :=
  namingWith ... (.positional signalType)
```

`withPorts` changes only external naming metadata. It preserves the module
key, structure, child-instance names, recursive child naming, and named wires.
It does not replace propagation of `typeNaming` through the recursive core:
without that propagation, only the outer boundary receives meaningful names.

Do not add per-module projection equations such as `naming_ports` or
`namingWith_ports` speculatively. The naming definition itself is sufficient
for ordinary construction and emission; add a theorem only when a concrete
consumer needs that public guarantee. Likewise, emitted-name uniqueness is an
emission concern, not a structural correspondence obligation. Emitters should
diagnose collisions rather than requiring every module to carry an unused
`portNames_nodup` proof.

When a builder would hide rather than clarify the construction, use the
contract-first structural pattern above. Recursive module families, indexed or
programmatically generated hierarchies, generic composition mechanisms, and
large architectural connection tables all commonly fit this pattern. Keep the
`module_design` or ordinary recursive structural definitions under
`Internal/`; do not move their complexity into `Foo.lean`. Avoid introducing a
builder description merely to reproduce that structure less clearly.

## Reader-facing style

Keep the main and derived files visually small as well as logically simple.
Open only namespaces that supply names actually used in the file. Prefer dot
notation for an operation associated with a value, such as
`description.ImplementsCycleContract`, instead of opening a deep namespace for
one declaration. Namespace depth used to organize the library should not become
vocabulary that every module author must understand.

Comments should explain hardware intent, a non-obvious guarantee, or a genuine
exception to the standard organization. Do not add a section heading around
one or two self-explanatory declarations, narrate what the following line
already says, or preserve historical commentary after the old approach has
been removed. A short module-level sentence and concise API documentation are
usually enough for `FooDerived.lean`.

Prefer declarations generated from the boundary over handwritten aliases and
adapters. Every repeated port name is an opportunity for the authored
construction, placement API, and generated structure to drift apart.

## `Foo.lean`: public definition and contract

The main file explains what the hardware is. It should contain, as applicable:

- a module-level description of the circuit and its purpose;
- the concise, hardware-oriented authored definition, when one exists;
- named functions or propositions that express the module's natural behavior;
- the exact cycle contract; and
- short, fundamental conversions that explain the meaning of that contract.

The authored definition should be the form a hardware author is expected to
read and write. The contract should state the behavior independently of the
implementation hierarchy. A reader should be able to see the ports, important
children or operations, output behavior, and state transition from this file.

### Natural contract vocabulary

A contract should express the module's intended behavior as natural Lean:
ordinary pure functions, arithmetic, finite collections, records, protocol
states, and explicit encodings at the port boundary. It should describe what
the module computes, not replay the sequence of children used to compute it.
The structure and its certification proof are responsible for connecting that
natural specification to gates, adapters, layouts, registers, and wiring.

For example, an unsigned partial-product row should first state its numerical
meaning and then encode that value at the output width:

```lean
def resultNat (width : Nat) (row : Nat)
    (multiplicand : Fin width → Bool) (selected : Bool) : Nat :=
  if selected then BitVector.toNat width multiplicand * 2 ^ row else 0

def resultValue ... :=
  BitVector.ofNat resultWidth (resultNat width row multiplicand selected)
```

Its contract should use `resultValue`; it should not define the result as a
`Mask` operation followed by a `VectorLayout` merely because that is the chosen
implementation. The certification proof establishes that those children
implement the numerical function.

“Natural” does not mean imprecise or detached from hardware. Wrapping,
truncation, saturation, bit ordering, latency, reset behavior, and protocol
assumptions must remain explicit whenever they are observable. Prefer a pure
Lean definition of those effects over a restatement of the structural
decomposition. A structural operation may appear directly in a contract when
that operation is itself the module's advertised behavior—for example, a
generic layout module whose purpose is exactly to apply a supplied layout.

Use this test when reviewing a contract: if the implementation changed to a
different hierarchy that computes the same result, the contract should usually
remain unchanged. If changing a child module, instance order, or wiring pattern
forces an otherwise behavior-preserving contract rewrite, the contract is
probably too implementation-shaped.

For a contract-first structural module, omit the authored definition and the
children or operations from this file. The reader should still see the complete
boundary behavior and state transition; the implementation hierarchy belongs
under `Internal/`.

An ordinary main file must not directly import an `Internal/` path, and its own
`Foo.Internal` structure or verification module must not occur in its import
closure. The dependency direction is the reverse: generated structure imports
the public boundary and contract, plus the authored construction when one
exists. A parent construction may import a child's `BarDerived.lean` facade in
order to place that child; the facade legitimately depends transitively on
`Bar.Internal`. The parent must depend on that public facade rather than import
the child's internal path itself. The main file should not contain child
certification maps, schedules, structural-solution proofs, or long tactic
proofs.

Code that needs only the specification may import this file and use:

- `Input`, `Output`, and `ports` for the boundary;
- the behavior and cycle-contract declarations when stating specifications.

## `FooDerived.lean`: public declarations backed by internals

The derived file imports `Internal/FooVerification.lean` and forms the complete
public facade. It may contain:

- placement helpers intended for authors of parent circuits;
- short `Silean.Authoring` abbreviations for common expression-like
  placements owned by this module;
- wrappers that consume the concrete `design`, `moduleStructure`, and naming
  declarations generated by the internal structure;
- useful consequences of the contract, stated at the module's natural level;
- either the authored module's implementation-independent
  `construction_correct` theorem or the structural module's concrete
  `implements_contract` theorem; and
- additional semantic results that are useful to proofs using the module.

These should be real reusable theorem interfaces, not duplicate propositions
created only to make the file look explanatory. Comments should explain the
roles of unfamiliar arguments and why a theorem is useful to a parent proof.

Proofs in this file should normally be a direct reference to a theorem under
`Foo.Internal`, or otherwise remain short. They may delegate to a
certification constructed in `Internal/FooVerification.lean`, but their
statements must not expose schedules, intermediate child proposals, or other
proof-specific choices unless those concepts are inherently part of the
module's public semantics.

For an authored module, use this concrete test for every public semantic
theorem statement: copy the statement to a file that imports only `Foo.lean`,
replace its proof with `by sorry`, and check that it elaborates. The real proof
in `FooDerived.lean` may be only a reference to `Foo.Internal`; the statement
must not require that import.

A contract-first structural module has one deliberate exception:
`implements_contract` names `moduleStructure` and the certification's state
correspondence because there is no authored description to quantify over.
Other semantic theorem statements should still depend only on the boundary and
contract vocabulary from `Foo.lean`. Even this structural correctness
statement must avoid raw wiring, generated child labels, schedules, and
proof-local helpers.

For example, the public correctness theorem should have this shape:

```lean
theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct
```

Public one-cycle theorems should use the shared boundary-step vocabulary:

- a contract theorem takes `step : cycleContract.Step` and a proof of
  `cycleContract.Allows step`; and
- a structural theorem takes `step : moduleStructure.Step` and a proof of
  `moduleStructure.Realizes step`.

This keeps `inputs`, `currentState`, `outputs`, and `nextState` together and
prevents structural witnesses from leaking into the public interface.
`IsSolution` and `HierStep` remain internal structural witnesses used to
establish `Realizes`. The superseded four-argument `EvaluatesTo` relation and
its compatibility layer have been removed; use `Allows`. Inline
`module_cycle_contract` rules generate one named projection for every written
output, such as `cycleContract.sum allowed`; use those projections instead of
adding handwritten aliases such as `sum_of_allowed`, or restating the output
equations in a separate `Behavior` proposition. A theorem that combines several
projections or states a result in more natural mathematical vocabulary is not
an alias and may still be useful. Introduce a second behavioral abstraction only
when it expresses a genuinely different guarantee, such as a transaction- or
trace-level contract.

When proving a parent module from its children, keep the returned
`ChildContractMatch` intact. Use `childMatch.ruleHolds rule` for one declared
output rule, `childMatch.boundaryOutput cycleContract.sumEquation` for a
generated output equation, `childMatch.boundaryFact theorem` for a genuinely
aggregate input/output property, and `childMatch.nextCorresponds` for state
threading. `childContractStep` is layer-certification machinery and should not
appear in module proofs.

Downstream verification code normally imports this file. In addition to its
named theorems, it may use:

- `certification`, when the module is a certified child of another module; and
- `certified`, when the complete packaged certified module is required; and
- `certifiedLayer`, when deliberately reusing the module body with a different
  family of children satisfying the same child contracts.

Importing `FooDerived.lean` also makes the definitions from `Foo.lean`
available, so downstream code should not separately import both.

## `Internal/FooStructure.lean`: expanded typed hardware

The structure file contains the mechanically explicit representation used by
the framework. It normally contains:

- reuse of the boundary and boundary naming declared in `Foo.lean`;
- the expanded `module_design` declaration;
- child-instance types and boundaries;
- total typed wiring;
- the resulting `ModuleBody` and `ModuleStructure`; and
- structural naming and `NamedModule` bundles.

This file exists because the explicit typed structure is useful to Lean,
emission, and verification but is usually noisier than the authored circuit.
It contains no behavioral correctness proof.

Some declarations generated in this file are deliberate public artifacts:
`moduleStructure`, `naming`, `namingWith`, `design`, and `designWith`. Their
physical location under `Internal/` keeps the normal reading path clean; they
are reached by ordinary users through `FooDerived.lean`.

Other generated declarations, such as raw contexts, child maps, wiring, and
module bodies, are structural implementation details. Downstream code should
not use them merely because Lean makes them visible through a transitive
import.

### Structural rules and contract-independent certification

Structural solvability is independent of behavioral specification.
`ModuleStructuralRules` describes only which boundary inputs a child rule reads
and which boundary outputs it makes available. A
`ModuleStructuralCertification` proves that the simultaneous equations have
exactly one solution for every boundary input and physical state; it does not
state what that solution means.

Cycle contracts automatically supply fine-grained structural rules by erasing
their behavioral targets, and cycle certifications automatically certify those
rules. A structurally certified module without a cycle contract can instead use
the conservative whole-module rule, which reads every input and writes every
output. Do not invent a deterministic cycle contract merely to make a custom
relational contract compositional.

Use the two canonical schedule commands according to the proof being built:

- `module_rule_schedules` supplies the output and state schedules needed by a
  cycle-contract certification; and
- `module_complete_schedule` supplies one contract-independent order covering
  every structural rule of every child.

A complete derived schedule can be instantiated with structurally certified
children and transported to a separately declared composite using
`DerivedCompleteSchedule.certifyComposite`. Keep the schedule private. Expose
only the resulting `structuralCertification` when downstream structural
composition needs it. `CarrySaveLayer` demonstrates fine-grained rules derived
from cycle-certified children; `CarrySaveTree` demonstrates automatic whole
rules for a recursive module with a custom relational contract.

## `Internal/FooVerification.lean`: proof construction

The verification file contains the details needed to build the public
certificate. For a cycle-contract module it normally contains:

- certified-child selection;
- output and state proof schedules;
- the relation between contract state and structural state;
- existence, uniqueness, and contract-implementation arguments;
- detailed authored-description correspondence proofs, unless kept in a
  separate `Internal/FooCorrespondence.lean` compilation unit; and
- construction of `certification` and `certified`.

For a custom relational contract, replace the cycle-only items with a complete
structural schedule, a public `ModuleStructuralCertification`, and a direct
theorem connecting every realization to the relational contract.

Proof-local declarations should be `private` whenever they are used only in
this file. A supporting declaration that must cross a Lean file boundary but
is not a supported API should live under `Foo.Internal`, so its name clearly
marks that status.

`certification` and `certified` are exceptions: although constructed in the
verification file, they are intentional public results. The former is the
compositional interface used when `Foo` is a child; the latter packages the
structure, contract, and certificate for general consumption.

Correspondence proofs should normalize builder implementation details through
the dedicated `circuit_description` simp set. A proof may explicitly add the
few child placement helpers used by its module:

```lean
simp only [circuit_description, description, construction,
  ChildA.place, ChildB.place]
```

Do not repeat the definitions of `build`, monadic bind, draft finalization,
wire resolution, and connection finalization in every module proof. Those are
owned by the authoring layer. Keep module-specific enumeration and port-name
facts explicit after normalization. For a sufficiently large module, put
correspondence and behavioral certification in separate, descriptively named
internal files so each independent check remains a small compilation unit.

When turning that correspondence and a certification into the public authored
correctness theorem, let the generated naming carry its own key, child names,
child naming, and named-wire metadata. Unfold it in a local copy of the
correspondence theorem, then provide only the structural body and children
needed to resolve the dependent types:

```lean
have corresponds := description_corresponds parameter
unfold Foo.naming at corresponds
simp only [id_eq] at corresponds
exact ImplementsCycleContract.of_certification
  (referenceBody := {
    instancePorts := instancePorts parameter
    wiring := wiring parameter })
  (children := structuralChildren parameter)
  corresponds (certification parameter)
```

Do not restate the module key, instance-name function, child naming, or named
wires in this proof. Those values already occur in `Foo.naming`; repeating them
makes the correctness bridge longer and creates another place for naming to
drift.

## The public boundary

An `Internal/` directory is an organizational convention, not a Lean access
modifier. Imports are transitive, and a declaration in an internal file is
still accessible unless it is declared `private`. Moreover, Lean's `private`
declarations cannot be referenced from a different source file.

The project therefore uses three reinforcing boundaries:

1. **Import boundary.** Code outside `Foo/` imports only `Foo.lean` or
   `FooDerived.lean`, never a path under `Foo/Internal/`.
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
- the declarations and theorems in `FooDerived.lean`; and
- its documented `structuralCertification` when it has no ordinary cycle
  certification but is intended for structural composition; and
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
import Silean.Modules.Foo.FooDerived

-- Referring only to the public boundary, behavior, or contract:
import Silean.Modules.Foo.Foo
```

`Silean.Modules` should import the derived file for an ordinary fully certified
module, making the complete supported interface available from the aggregate.
Internal files must not be imported by unrelated modules as a shortcut around
the public façade.

An ordinary main file never imports a path under its own `Internal/` directory.
`FooDerived.lean` is the single public exception: it is the facade specifically
intended to turn internal generated artifacts into a supported API. Code
outside the module imports the main or derived file.

## Variations

The four-file layout should be adapted when the module's semantics require it:

- A primitive or simple leaf may keep its definition, contract, and short
  proof together when splitting them would make navigation worse.
- Existing modules may retain a `FooTheorems.lean` facade until migrated. New
  human-first modules should use `FooDerived.lean` when the same facade also
  owns placement or other public declarations backed by generated internals.
- A module refined through several abstraction levels may have a separate
  public file for each independently useful contract, such as exact-cycle and
  FIFO behavior.
- A large proof may use several files under `Internal/`, named for their proof
  responsibilities rather than numbered as arbitrary chunks.
- A private child meaningful only as part of its parent may live in a
  subdirectory of that parent instead of becoming a top-level reusable module.
- A generic composition mechanism parameterized by arbitrary certified
  children may live under `Composition/` rather than imitate a concrete module
  directory. Its public certification constructor should be named for that
  role, while its schedules and proof-local helpers remain private.

`Equality`, `BinaryToOneHot`, `CombMuxTree`, and `RegisterBank` are completed
examples of the contract-first structural pattern. `EqualsConstant` is the
authored comparison counterpart. Their direct PicoRV clients—`Alu`, `Regs`,
and `MemoryLookahead`—show the authored pattern at larger scale: their main
files own typed constructions and contracts, while placement and generated
correctness live in `Derived` facades. `Register`, `Add`, `Increment`, and
`SerialDepthFifo` provide further completed examples.

The register-to-FIFO stack shows that distinct contracts do not require one
public file per proof layer. `OneEntryFifo.lean` owns the exact-cycle behavior;
`OneEntryFifoDerived.lean` exposes both exact structural certification and the
separate capacity-one abstract queue guarantee. Their statements remain
distinct even though the internal-backed public results share one facade.
`OneEntryFifo/Control/` remains a private child beneath the only parent for
which its handshake decisions are meaningful.

Additional files should correspond to concepts a reader or maintainer can
name. They should not split a linear proof merely to reduce file length.

## Checks and examples

Compilation examples and regression checks belong under
`tests/silean/lean/SileanTests/`, not in the module's reader-facing files. They should
import the same public façade expected of downstream users. This checks both
the declarations and the intended import boundary.

The main and derived files may still contain small checked `example`
declarations when those examples materially teach a type or authoring form.
Such examples should be unmistakably illustrative and must not be dependencies
of production code.
