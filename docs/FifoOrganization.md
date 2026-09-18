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
| `Modules/OneEntryFifo/Internal/OneEntryFifoStructure.lean` | Expanded typed hierarchy used by verification and emission |
| `Modules/OneEntryFifo/Internal/OneEntryFifoVerification.lean` | Child selection, schedules, structural certification, and authored-description correspondence |
| `Modules/OneEntryFifo/Control/OneEntryFifoControl.lean` | Readable gate-level definition and exact contract of the private combinational control child |
| `Modules/OneEntryFifo/Control/OneEntryFifoControlTheorems.lean` | Public-to-the-parent control equations and implementation theorem |
| `Modules/OneEntryFifo/Control/Internal/` | Expanded control structure and gate-level certification details |
| `Modules/OneEntryFifo/OneEntryFifoCycleTheorems.lean` | Step-based exact-cycle laws, authored correspondence, and structural implementation theorem |
| `Modules/OneEntryFifo/OneEntryFifoCycleBehavior.lean` | Small adapter exposing the certified exact behavior to serial FIFO composition |
| `Modules/OneEntryFifo/Internal/OneEntryFifoFifoVerification.lean` | Capacity-one logical-queue refinement proof |
| `Modules/OneEntryFifo/OneEntryFifoFifoTheorems.lean` | Public capacity-one FIFO certification |
| `Composition/FifoSerialComposition.lean` | Generic two-child serial structural layer |
| `Composition/FifoSerialCertification.lean` | Exact-cycle certification using only the two public child contracts |
| `Composition/FifoSerialRefinement.lean` | Generic composition of two child FIFO refinements; downstream contents precede upstream contents and the internal transfer cancels |
| `Naming/FifoSerialNaming.lean` | Presentation names for the generic serial hierarchy |
| `Modules/SerialDepthFifo/SerialDepthFifo.lean` | Recursive positive-depth structure, natural exact-cycle behavior, naming, and complete design bundles; documents why builder duplication would obscure this generated family |
| `Modules/SerialDepthFifo/Internal/SerialDepthFifoVerification.lean` | Recursive structural certification for every positive depth |
| `Modules/SerialDepthFifo/SerialDepthFifoCycleTheorems.lean` | Step-based exact-cycle interface and implementation theorem |
| `Modules/SerialDepthFifo/Internal/SerialDepthFifoFifoVerification.lean` | Recursive abstract FIFO refinement proof |
| `Modules/SerialDepthFifo/SerialDepthFifoFifoTheorems.lean` | Public FIFO certification with capacity equal to depth |
| `Modules/Fifo/Fifo.lean` | Pointer/register-bank structure and exact cycle contract |
| `Modules/Fifo/FifoPointerControl.lean` | Private pointer interpretation and transfer-control child used by the FIFO built from a register bank and pointers |
| `Modules/Fifo/FifoPointerControlTheorems.lean` | Public pointer-control behavior and implementation theorem |
| `Modules/Fifo/Internal/FifoPointerControlVerification.lean` | Pointer-control schedules and structural certification |
| `Modules/Fifo/FifoCycleTheorems.lean` | Public exact-cycle laws and implementation theorem for the pointer FIFO |
| `Modules/Fifo/Internal/FifoCycleVerification.lean` | Pointer-FIFO structural certification |
| `Modules/Fifo/FifoProperties.lean` | Circular-buffer occupancy, logical contents, invariant, and one-cycle queue lemmas |
| `Modules/Fifo/Internal/FifoFifoVerification.lean` | Pointer-FIFO logical-queue refinement proof |
| `Modules/Fifo/FifoFifoTheorems.lean` | Public capacity-`2^addressWidth` FIFO certification |

The former FIFO `*Certified.lean` import shims have been removed. New proof
code imports the theorem files above; structural details and refinement
witnesses are not a supported downstream interface.

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
