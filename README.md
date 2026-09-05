# Silean

WARNING:  On a scale of 0 to 10, where 0 is a project I wrote myself, and 10 is
a project entirely written by an LLM, this project is an 8.

My main role has been setting goals and keeping it going in vaguely the right
direction.  It's an experiment to see if a proof-assistant-embedded approach to
hardware design is practical yet. The "documentation" files are all LLM
generated at the moment and I wouldn't trust them too much.

About two years ago I had a go at writing an HDL embedded in dafny
([Silemma](https://github.com/benreynwar/silemma)).  I made some
progress, but it ended up being too difficult for me.  Now that LLMs have
gotten pretty good at writing proofs I decided it was time to have another go,
but this time using Lean4 and an LLM.

The rest of this README is LLM generated.

## Goal

Silean is an experiment in describing and verifying hardware in the same
Lean program. The goals are deliberately broad:

- the shape of a design should be hierarchical and structural, and should feel
  familiar to a hardware designer; and
- it should be practical to prove useful properties about that design.

The current approach combines type-safe wiring, order-independent structural
semantics, independent behavioral contracts, and direct FIRRTL traversal of
the hardware hierarchy.

## Current implementation

The most complex design currently implemented is a generic FIFO with
`2 ^ addressWidth` entries. Its hardware is assembled from a register bank,
extended read and write counters, and combinational pointer-control logic. The
extra pointer bit distinguishes full from empty when the storage addresses are
equal. The FIFO has synchronous reset and a standard valid/ready boundary.

This is an end-to-end example rather than only a collection of isolated
lemmas. Its hierarchy can be emitted directly as FIRRTL, its exact cycle
behavior is certified against the structural equations, and that behavior is
further proved to satisfy a latency-independent FIFO contract. The proof
establishes bounded capacity and that produced payloads are an ordered prefix
of accepted payloads; the sequences are equal when the FIFO is drained. There
are also one-entry and serially composed FIFOs, but the register-bank FIFO is
the largest individual hardware design currently in the project.

## The hardware model

Signals are recursively typed as bits, vectors, and tuples. `SignalMap` adds
symbolic labels to collections of these signal types, and `ModulePorts` uses
those maps to describe a module's inputs and outputs.

A `ModuleStructure` is the typed hierarchical definition of a module. It may
contain explicit behavioral blackboxes while a design is being assembled:

```lean
inductive ModuleStructure : ModulePorts → Type 1
  | primitive (primitive : Primitive) : ModuleStructure primitive.ports
  | blackbox (behavior : Primitive) : ModuleStructure behavior.ports
  | splitter (splitter : Composition.SignalSplitter) : ModuleStructure splitter.ports
  | combiner (combiner : Composition.SignalCombiner) : ModuleStructure combiner.ports
  | composite (body : ModuleBody)
      (childStructure : (name : body.context.instancePorts.Name) →
        ModuleStructure (body.context.instancePorts.ports name)) :
      ModuleStructure body.context.ports
```

The five forms are:

- `primitive`: a leaf operation with its own output and next-state equations;
- `blackbox`: an explicitly opaque leaf with assumed boundary equations;
- `splitter`: structural wiring that exposes the immediate components of a
  vector or tuple;
- `combiner`: structural wiring that assembles immediate components into a
  vector or tuple; and
- `composite`: a wired collection of named child modules, each of which has
  its own `ModuleStructure`.

`ModuleStructure.HasNoBlackboxes` recursively certifies that every leaf has a
concrete Silean structure. Closed synthesis entry points require this proof;
ordinary rendering remains available for staged designs and intentional
external modules.

A composite's body is an uninstantiated structural layer. It contains its
boundary, named child-instance boundaries, and complete wiring, but does not
choose implementations for those children:

```lean
structure ModuleBody where
  context : EndpointContext
  wiring : Wiring context.ports context.instancePorts
```

A primitive is a leaf whose output and next-state equations are given
directly:

```lean
structure Primitive where
  ports : ModulePorts
  localState : SignalMap
  outputReads : List ports.inputs.Label
  outputValues : ports.inputs.Values → localState.Values → ports.outputs.Values
  nextStateValues : ports.inputs.Values → localState.Values → localState.Values
  outputRespectsReads : ...
```

These types ensure that every connection joins signals of the same shape and
that every child input and module output has a driver. Fan-out is expressed by
using the same source more than once. Structural splitters and combiners take
vectors and labelled tuples apart and put them back together. Authoring
`SignalSchema` values are hierarchical FIRRTL naming trees indexed by their
name-independent `SignalType`; `signal_schema` declarations generate the typed
field labels and `SignalMap` used to refer to aggregate components. Schemas do
not enter structures, wiring, contracts, or proofs. A module's state is
derived recursively from the local state owned by its primitive leaves.

This supports familiar hierarchical construction. Generic modules such as
registers, muxes, equality, decoders, register banks, counters, and FIFOs are
assembled from certified children. Vectors and tuples are generally handled by
splitting them into immediate components, applying recursively constructed
modules, and combining the results again.

## What a circuit means

The structural meaning of one clock cycle is
`ModuleStructure.IsSolution`. Given boundary inputs and current structural
state, a `ProposedValues` supplies all boundary outputs, child values, and
primitive next states. It is a solution when all primitive equations, child
equations, and wiring equations hold.

This is a relation, not an algorithm. It says which values satisfy the circuit
without choosing an order in which to evaluate its components. Consequently,
feedback through storage is meaningful, while unsupported combinational loops
cannot gain an accidental meaning from a particular evaluator. The same
relation is chained to define execution over finite sequences of cycles.

## Contracts and proofs

Behavior is specified independently of structure. The project currently has
three contract forms which illustrate how contracts can build from exact local
behavior toward more abstract externally visible properties.

### Exact cycle contracts

`Contracts.Cycle.ModuleCycleContract` is the foundation. It has its own
behavioral state, a set of named output rules, and one complete next-state rule.
Each output rule declares exactly which inputs it reads and which outputs it
writes. These partial boundaries are typed, label-preserving `SignalGroup`
values, so rule behavior uses signal names rather than positional tuples. The
contract says what a module does on one cycle, but says nothing
about its child instances, wiring, or evaluation schedule. For example, a
register-bank contract is phrased in terms of reading and updating a vector of
values, not in terms of its decoder, mux tree, and individual registers.

A `Contracts.Cycle.ModuleCycleCertified` packages a structure and a contract with proofs that:

1. every structural state corresponds to some abstract contract state;
2. a structural solution exists for every input and current state;
3. that solution is unique; and
4. every structural solution produces the outputs and next state required by
   the contract, while preserving the state correspondence.

The fourth item is the main refinement theorem. Quantifying over every
structural solution is important: correctness does not depend on a chosen
evaluator or on the proof used to establish uniqueness.

Proofs are compositional. When proving a composite module, each child is used
through its public contract and certification rather than by unfolding its
implementation. The parent's wiring connects those child-level facts into the
parent contract. Parent-owned certified schedules record which child contract
rules make each result available. Generic schedule machinery uses them to
construct a structural solution and prove that it is the only solution; the
schedules are proof witnesses and do not define the equations' meaning.

The preferred composition interface is structure-first. `ModuleBody` declares
one uninstantiated structural layer: named child boundaries and wiring, but no
child implementations. `ModuleCycleCertifiedLayer` proves that this fixed
layer implements its parent contract for *every* family of child structures
certified against the declared child contracts. Contract-only schedules are
part of that proof and therefore cannot depend on a chosen child hierarchy.
Concrete child structures are selected separately and `instantiate` combines
them with the certified layer. HalfAdder and FullAdder validate this boundary,
with directly computable structures and opaque exported proof objects.

### Reset-synchronized contracts

`Contracts.Reset.ModuleResetContract` moves from one-cycle correspondence to
trace behavior. A trace may begin from an unknown hardware state, so behavior
before reset is unconstrained. Reset synchronizes the specification, after
which every cycle must match. Its specification state may be any Lean type and
does not require an exposed mapping to structural state. Outputs can be
specified as zero, one, or `dontCare` on each cycle.

This form is useful when exact cycle timing matters but reproducing the
implementation's state layout would make the specification unnatural or
unwieldy.

### Latency-independent FIFO contracts

`Contracts.Fifo.FifoContract` is more abstract still. It observes valid/ready
transfers at the input and output interfaces rather than requiring outputs to
match on particular cycles. After reset, it tracks an abstract bounded queue
and requires every produced payload to be the next queued accepted payload;
unproduced inputs remain in the queue. Both combinational fall-through and
registered latency are allowed.

The register-bank FIFO demonstrates how these levels compose. Its structural
implementation is first certified against an exact cycle contract. A private
refinement maps that cycle contract's pointer-and-storage state to an abstract
Lean `List`, proving the public latency-independent FIFO contract. The final
FIFO certificate exposes the structure and abstract FIFO guarantee; the
state-mapping details remain private proof machinery. After reset, accepted
and produced transfers obey the abstract bounded-queue transition on every
subsequent non-reset cycle. Consequently, produced payloads are an ordered
prefix of accepted payloads, and the sequences are equal once the FIFO is
drained.

As more complex designs are added, we expect to need both additional
general-purpose contract forms and custom theorems expressing the important
properties of particular modules.

## What is and is not proved

WARNING: Just a quick reminder from that the content here (but not these two sentences)
was written by an LLM.  I'm not yet confident myself about exactly what is and
isn't proven.

Lean proves the connection from `ModuleStructure`'s simultaneous equations to
the cycle contracts and onward to the reset and FIFO trace contracts described
above. The exported FIFO certificate contains existence and uniqueness of each
structural result, so its correctness theorem is not made vacuous by an
inconsistent circuit. The development contains no `sorry`, `admit`,
project-defined axiom, or unsafe definition. `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for
`Silean.Modules.Fifo.fifoCertified` and its public structure and contract
projections.

The FIRRTL renderer is not yet proved semantics-preserving. Its metadata is
dependent on the exact `ModuleStructure`, preventing a supported primitive
from being named as a different operation, and generated FIRRTL is compiled
and tested with firtool, Verilator, and cocotb. Nevertheless, the current
formal claim ends at the structural model rather than the generated FIRRTL or
SystemVerilog.

The structural semantics are also two-state: signal values are Lean `Bool`s.
They do not model `X`, `Z`, analogue behavior, timing, metastability, or clock
domain crossings. Reset-synchronized contracts avoid assuming a particular
Boolean power-up state, but this is not a four-state initialization proof.

## Building and running

The recommended environment is the checked-in Nix flake. From the repository
root, enter it with:

```sh
nix develop
```

Build and check all Lean definitions and proofs with:

```sh
lake build
```

Check that every focused `*Checks.lean` regression is included by the explicit
`SileanExamples.lean` aggregate with:

```sh
make check-example-imports
```

Run the complete generated-hardware regression with:

```sh
make test
```

This emits configured designs as FIRRTL, lowers them to SystemVerilog with
CIRCT `firtool`, compiles them with Verilator, and runs their cocotb tests. The
generated files and simulator builds are placed under `build/`.

Individual hardware regressions can be run with:

```sh
make test-bit-register
make test-structured-fifo
make test-serial-fifo
make test-register-bank
make test-pointer-fifo
```

The corresponding `firrtl-*` and `verilog-*` targets stop after emission or
SystemVerilog generation. For example:

```sh
make firrtl-pointer-fifo
make verilog-pointer-fifo
```

Use `make clean` to remove generated build artifacts.

## Where to look

- [`Silean/Foundation/`](Silean/Foundation/) defines signal types, labelled
  maps, selections, ports, and state shapes.
- [`Silean/Structure/`](Silean/Structure/) defines instances, endpoints,
  wiring, module bodies, and recursive module structures.
- [`Silean/Authoring/`](Silean/Authoring/) provides concise module declarations
  and parameterizable `signal_schema` declarations. These generate an aggregate
  `SignalType`, its labelled `SignalMap`, hierarchical naming metadata, and
  typed field accessors without changing structural shape compatibility.
- [`Silean/Modules/`](Silean/Modules/) contains the reusable hardware,
  contracts, and certification proofs.
- [`docs/Architecture.md`](docs/Architecture.md) gives the detailed current
  design, and [`docs/SourceMap.md`](docs/SourceMap.md) maps concepts to files.
- [`Roadmap.md`](Roadmap.md) records the current direction and remaining work.

The checked-in Nix flake supplies Lean, CIRCT, Verilator, and the Python/cocotb
simulation tools used by the `Makefile` regressions.
