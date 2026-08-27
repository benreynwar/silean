# Silean 2 roadmap

This roadmap records the current destination and remaining work. The current
design is described in `docs/Architecture.md`; source ownership is summarized
in `docs/SourceMap.md`.

## Direction

Silean 2 represents hardware as a typed recursive hierarchy with total wiring
and primitive storage. Its meaning is the order-independent
`ModuleStructure.IsSolution` relation. Independently declared cycle contracts
describe observable behavior, and certification proves that every structural
solution implements its contract. Module certificates supply structural
existence; certified schedules establish uniqueness.

The same computable hierarchy is consumed directly by naming and FIRRTL
generation. We do not lower to a second semantic netlist, and backend
translation is not part of the correctness proof at this stage.

## Established foundation

- Bits, vectors, and heterogeneous tuples have typed values and stable finite
  labels.
- Module ports contain connectivity only; structural state is derived from
  primitive storage and recursive child ownership.
- Instances, endpoints, and total typed wiring describe composite structure.
- Structural equations have an evaluation-order-independent meaning.
- Cycle contracts own independent abstract state, rule-local output
  dependencies, and an explicit-input next-state rule.
- Certified child rules and output/state schedules establish hierarchical
  availability and structural uniqueness without becoming circuit semantics.
- `ModuleCycleCertified` packages a computable structure, cycle contract, state
  correspondence, refinement proof, and structural existence/uniqueness.
- Generic Register, Mask, BitwiseOr, Mux, EnabledRegister, OneEntryFifo, serial
  FIFO composition, and arbitrary positive-depth FIFO validate the hierarchy.
- Temporal FIFO contracts prove conservation, capacity, and ready-propagation
  behavior over contract execution.
- Module-owned naming feeds direct FIRRTL generation; FIRRTL is converted to
  SystemVerilog and exercised with Verilator and cocotb.

## Working constraints

- Keep structure, contracts, proof schedules, naming, and backend rendering in
  separate ownership layers.
- Treat stateless modules as having zero-bit state, not as a separate kind.
- Prefer fully generic proof laws; do not add helpers specialized to one module
  merely to shorten a proof.
- Keep module structures computable and proof packages opaque when needed.
- Do not introduce lowering or raw numeric identities as semantic
  prerequisites.
- Keep focused Lean targets below five seconds.
- Do not use `sorry`, new axioms, `Classical.choice`, or `native_decide`.

## Completed repository cleanup

The repository-facing semantic-no-op cleanup established:

- one authoritative architecture document and one source map;
- aggregate imports reflecting directory ownership;
- removal of provisional APIs with no real consumer;
- separate test fixtures and regression checks; and
- verified Lean, FIRRTL conversion, and cocotb regressions.

## Next architectural goal

Reduce the repeated recursive split/component/combine certification machinery
in Register, Mask, and BitwiseOr.

The abstraction must be generic over aggregate shape, split inputs, broadcast
inputs, recursive certified children, component behavior, and state
correspondence. Register should exercise the stateful case first; Mask and
BitwiseOr should then demonstrate that the abstraction also covers distinct
combinational layouts. Retain the abstraction only if it materially reduces
module code while leaving the wiring and proof boundary easier to understand.

## Later work

1. Consolidate FIFO organization around interface behavior, one-entry storage,
   serial composition, positive depth, and temporal properties. Hide recursive
   implementation helpers that are not public module APIs.
2. Review intentionally public module theorems and remove debugging or
   construction details that no consumer needs.
3. Expand direct FIRRTL emission to additional configured designs as useful;
   keep translation straightforward and executable rather than proof-heavy.
4. Add reset semantics only when a concrete module requires them.
5. Consider backend correctness or trace packaging only when a real consumer
   makes the additional proof layer valuable.

Each architectural goal ends with a plain-language review, focused timing,
full Lean verification, and relevant external simulation.
