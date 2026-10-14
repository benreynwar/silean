# FIFO organization

All FIFO implementations use `Interfaces/FifoPorts.lean`. Its
`Silean.Interfaces.Fifo` namespace owns the
canonical input/output labels and defines the two boundary interfaces:
`Interfaces.ValidReadySink` for traffic entering the FIFO and
`Interfaces.ValidReadySource` for
traffic leaving it. Interfaces identify and interpret ports; they do not state
FIFO ordering or expose implementation state.

## Public behavioral contract

`Contracts/Fifo/FifoContract.lean` defines the latency-independent
`Contracts.Fifo.FifoContract`. It owns:

- one valid/ready sink and one valid/ready source with the same payload shape;
- a synchronous reset input;
- a capacity;
- boundary input and output transfers derived from the interfaces; and
- a reset-synchronized finite-trace relation over a logical bounded queue.

Behavior is unconstrained before the first reset and on each reset cycle. The
state following reset is the empty logical queue. On ordinary synchronized
cycles the queue equation is

`oldQueue ++ acceptedInput = acceptedOutput ++ nextQueue`.

This equation permits fall-through and registered implementations without
constraining latency or internal state. Generic trace laws prove conservation
over reset-free synchronized suffixes, output ordering from an empty queue,
and the capacity bound on every synchronized logical queue.

`Contracts.Fifo.FifoCertified` pairs a structure with this contract. Its `hasSolution` field
requires a structural result for every structural state and cycle input, so an
inconsistent structure cannot satisfy refinement vacuously. Its implementation
field says every finite structural execution is accepted by the contract.

## Proof bridge

`Contracts/Fifo/FifoCycleRefinement.lean` defines the private-proof adapter used
by current implementations. A `Contracts.Fifo.FifoCycleRefinement` supplies an invariant and a logical
queue interpretation for an already cycle-certified module. It proves reset
establishment, ordinary-cycle queue preservation, and the capacity bound. The
adapter then performs the trace induction and produces a public
`Contracts.Fifo.FifoCertified`; neither the invariant nor the state interpretation appears in
that result.

## Implementations

| Source | Responsibility |
| --- | --- |
| `Modules/OneEntryFifo/OneEntryFifo.lean` | Readable one-entry feedback circuit and natural exact-cycle contract |
| `Modules/OneEntryFifo/OneEntryFifoDerived.lean` | Placement, authored correctness, exact-cycle certification, and capacity-one FIFO certification |
| `Modules/OneEntryFifo/Internal/OneEntryFifoStructure.lean` | Expanded typed hierarchy used by verification and emission |
| `Modules/OneEntryFifo/Internal/OneEntryFifoVerification.lean` | Child selection, schedules, structural certification, and authored-description correspondence |
| `Modules/OneEntryFifo/Control/OneEntryFifoControl.lean` | Readable gate-level definition and exact contract of the private combinational control child |
| `Modules/OneEntryFifo/Control/OneEntryFifoControlDerived.lean` | Control placement and authored correctness |
| `Modules/OneEntryFifo/Control/Internal/` | Expanded control structure and gate-level certification details |
| `Modules/OneEntryFifo/Internal/OneEntryFifoFifoVerification.lean` | Capacity-one logical-queue refinement proof |
| `Composition/FifoSerialComposition.lean` | Generic two-child serial structural layer |
| `Composition/FifoSerialCertification.lean` | Exact-cycle certification using only the two public child contracts |
| `Composition/FifoSerialRefinement.lean` | Generic composition of two child FIFO refinements; downstream contents precede upstream contents and the internal transfer cancels |
| `Naming/FifoSerialNaming.lean` | Presentation names for the generic serial hierarchy |
| `Modules/SerialDepthFifo/SerialDepthFifo.lean` | Natural recursive exact-cycle behavior, contract, and contract laws |
| `Modules/SerialDepthFifo/SerialDepthFifoDerived.lean` | Naming, design, placement, exact certification, and FIFO certification |
| `Modules/SerialDepthFifo/Internal/SerialDepthFifoStructure.lean` | Recursive positive-depth structural hierarchy |
| `Modules/SerialDepthFifo/Internal/SerialDepthFifoVerification.lean` | Recursive structural certification for every positive depth |
| `Modules/SerialDepthFifo/Internal/SerialDepthFifoFifoVerification.lean` | Recursive abstract FIFO refinement proof |
| `Modules/Fifo/Fifo.lean` | Readable pointer/register-bank construction, exact contract, laws, and logical queue definitions |
| `Modules/Fifo/FifoDerived.lean` | Placement, authored correctness, exact certification, and bounded FIFO certification |
| `Modules/Fifo/FifoPointerControl.lean` | Readable pointer-control construction, exact equations, and mathematical laws |
| `Modules/Fifo/FifoPointerControlDerived.lean` | Pointer-control placement and authored correctness |
| `Modules/Fifo/Internal/FifoPointerControlVerification.lean` | Pointer-control schedules and structural certification |
| `Modules/Fifo/Internal/FifoCycleVerification.lean` | Pointer-FIFO structural certification |
| `Modules/Fifo/FifoProperties.lean` | Compact public queue-property theorem interface |
| `Modules/Fifo/Internal/FifoPropertiesVerification.lean` | Circular-buffer arithmetic and queue-property proof implementation |
| `Modules/Fifo/Internal/FifoFifoVerification.lean` | Pointer-FIFO logical-queue refinement proof |

Downstream construction and certification code imports the corresponding
`*Derived.lean` facade. Code that needs only a FIFO's behavior or exact
contract imports its main file. Structural details and refinement witnesses
are not a supported downstream interface.

The three `Composition/FifoSerial*` files are a generic composition mechanism,
not one concrete reusable module. `FifoSerialCertification.lean` therefore
exports the certification combinator itself instead of adding an artificial
module theorem façade. Its schedule, state relation, and implementation lemmas
remain private; downstream code uses only `certifiedLayer`, `certification`, or
`certifiedCycleBehavior`.

The serial composition proof consumes only child cycle behaviors and FIFO
refinements. It does not inspect either child structure or the schedules used
to certify it. The pointer implementation uses its public cycle contract and
logical circular-buffer lemmas; it does not retain a separate FIFO evaluator
or trace-view API.

## Separation from generation

FIRRTL generation consumes only `ModuleStructure` and naming metadata. FIFO
contracts, logical queues, invariants, and proof adapters are not required to
render a circuit. Synchronous reset remains ordinary module wiring and state
behavior: current outputs are from the pre-edge state, while the following
logical FIFO state is empty.
