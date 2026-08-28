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

## The hardware model

Signals are recursively typed as bits, vectors, and tuples. `SignalMap` adds
symbolic labels to collections of these signal types, and `ModulePorts` uses
those maps to describe a module's inputs and outputs.

A `ModuleStructure` is the complete hierarchical definition of a module:

```lean
inductive ModuleStructure : ModulePorts → Type 1
  | primitive (primitive : Primitive) : ModuleStructure primitive.ports
  | splitter (splitter : SignalSplitter) : ModuleStructure splitter.ports
  | combiner (combiner : SignalCombiner) : ModuleStructure combiner.ports
  | composite (body : ModuleBody)
      (childStructure : (name : body.context.instances.Name) →
        ModuleStructure (body.context.instances.ports name)) :
      ModuleStructure body.context.ports
```

The four forms are:

- `primitive`: a leaf operation with its own output and next-state equations;
- `splitter`: structural wiring that exposes the immediate components of a
  vector or tuple;
- `combiner`: structural wiring that assembles immediate components into a
  vector or tuple; and
- `composite`: a wired collection of named child modules, each of which has
  its own `ModuleStructure`.

A composite's body contains its boundary, named child instances, and complete
wiring:

```lean
structure ModuleBody where
  context : EndpointContext
  wiring : Wiring context.ports context.instances
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
vectors and tuples apart and put them back together, while a module's state is
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

Behavior is specified independently of structure. The most basic contract form
is `ModuleCycleContract`. It has its own abstract state, a set of named output
rules, and a next-state rule. Each output rule declares exactly which inputs it
reads and which outputs it writes. The contract says what a module does, but
says nothing about its child instances, wiring, or evaluation schedule. For
example, a register-bank contract is phrased in terms of reading and updating a
vector of values, not in terms of its decoder, mux tree, and individual
registers.

A `ModuleCycleCertified` packages a structure and a contract with proofs that:

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
rules make each result available; these schedules prove that the structural
equations have at most one solution, but they do not define the equations'
meaning. Existence is proved separately, usually by constructing a proposal
from the existence guarantees of the certified children.

Cycle contracts are not intended to be the only kind of contract. A
`ModuleResetContract` specifies behavior over a trace beginning from an unknown
hardware state. Before reset it places no requirements on the outputs; reset
synchronizes the specification, after which each cycle must follow the
contract. Certification is then a direct relation between structural and
contract traces, with no exposed correspondence between their internal states.

Removing that state-correspondence requirement allows the specification state
to take a more natural form than the implementation state. For example, the
reset contract for a FIFO can describe its contents as a `List` of data rather
than reproducing the implementation's circular buffer, pointers, and storage.
From there, module-specific theorems establish properties such as capacity,
conservation of data, and FIFO ordering.

As more complex designs are added, we expect to need both additional
general-purpose contract forms and custom theorems expressing the important
properties of particular modules.

## Where to look

- [`Silean/Foundation/`](Silean/Foundation/) defines signal types, labelled
  maps, selections, ports, and state shapes.
- [`Silean/Structure/`](Silean/Structure/) defines instances, endpoints,
  wiring, module bodies, and recursive module structures.
- [`Silean/Modules/`](Silean/Modules/) contains the reusable hardware,
  contracts, and certification proofs.
- [`docs/Architecture.md`](docs/Architecture.md) gives the detailed current
  design, and [`docs/SourceMap.md`](docs/SourceMap.md) maps concepts to files.
- [`Roadmap.md`](Roadmap.md) records the current direction and remaining work.
- [`docs/PicoRV32ModuleHierarchy.md`](docs/PicoRV32ModuleHierarchy.md) records
  the provisional module and contract plan for the long-term direct PicoRV32
  port.
- [`docs/PicoRV32TopLevelPlan.md`](docs/PicoRV32TopLevelPlan.md) refines that
  direction into the proposed top-level children, state ownership, signal
  flow, and proof-staging order.

The project builds with `lake build`. The checked-in Nix flake supplies Lean,
CIRCT, Verilator, and the Python/cocotb simulation tools used by the `Makefile`
regressions.
