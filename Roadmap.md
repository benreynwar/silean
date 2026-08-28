# Silean roadmap

This roadmap records the current destination and remaining work. The current
design is described in `docs/Architecture.md`; source ownership is summarized
in `docs/SourceMap.md`.

## Direction

Silean represents hardware as a typed recursive hierarchy with total wiring
and primitive storage. Its meaning is the order-independent
`ModuleStructure.IsSolution` relation. Independently declared behavioral
contracts describe what users may observe, and separate certifications connect
them to structure. The existing cycle contracts support rule-local
hierarchical reasoning and an explicit correspondence between contract and
structural state. They are one contract form rather than a requirement for all
future modules. Module certificates supply structural existence; certified
schedules establish uniqueness.

The same computable hierarchy is consumed directly by naming and FIRRTL
generation. We do not lower to a second semantic netlist, and backend
translation is not part of the correctness proof at this stage.

## Established foundation

- Bits, vectors, and heterogeneous tuples have typed values and stable finite
  labels.
- Ternary zero/one/don't-care expectations retain those same recursive shapes
  and labelled maps, with generic componentwise matching laws.
- Reset-synchronized contracts use arbitrary Lean state and specify exact-cycle
  ternary output expectations after synchronous reset, with no structural-state
  mapping or dependency on another contract form.
- Module ports contain connectivity only; structural state is derived from
  primitive storage and recursive child ownership.
- Instances, endpoints, and total typed wiring describe composite structure.
- Structural equations have an evaluation-order-independent meaning.
- Contract-independent structural transitions chain those equations across
  finite input lists; per-cycle existence and uniqueness lift to unique finite
  output traces and final structural states without selecting an evaluator.
- Cycle contracts own independent abstract state, rule-local output
  dependencies, and an explicit-input next-state rule.
- Certified child rules and output/state schedules establish hierarchical
  availability and structural uniqueness without becoming circuit semantics.
- `ModuleCycleCertified` packages a computable structure, cycle contract, state
  correspondence, refinement proof, and structural existence/uniqueness.
- Generic Constant, balanced Reduction, All, recursive Equality, VectorConcat,
  BinaryToOneHot, CombMuxTree, RegisterBank, HalfAdder, Increment, Register, Mask,
  BitwiseOr, Mux,
  EnabledRegister,
  OneEntryFifo, serial FIFO composition, and arbitrary positive-depth FIFO
  validate the hierarchy.
- `LeafwiseComposition` provides the shared recursive/fixed-input
  split/component/combine hierarchy, proposal-existence construction, and
  component-family scheduling used by Constant, Register, Mask, and BitwiseOr.
- FIFO cycle behavior, execution, and derived properties are separate layers.
  The properties prove conservation, capacity, and ready propagation over
  contract execution.
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

## Completed leafwise composition review

Register, Mask, and BitwiseOr now share a generic aggregate hierarchy and one
generic structural-existence proof. Register validates recursive state, Mask
validates a broadcast bit beside one recursive input, and BitwiseOr validates
two recursive inputs. Their schedules retain the contract-specific dependency
facts, while their state-correspondence and refinement proofs retain the actual
operation semantics. The retention boundary and comparison are recorded in
`docs/LeafwiseComposition.md`.

## Completed FIFO organization review

FIFO organization is consolidated around the shared interface, cycle behavior,
one-entry storage, serial composition, positive depth, execution, and derived
properties. Module structures remain free of execution data; proof-construction
schedules and witnesses are private. The resulting organization and its
retention decisions are recorded in `docs/FifoOrganization.md`.

## Completed constant generation

A Boolean constant primitive and certified generic `Constant T value` module
now generate arbitrary bit, vector, and tuple values. Aggregate constants use
the leafwise component/combiner hierarchy with empty input families and
value-dependent recursive leaves. Naming keys include the flattened value, and
direct FIRRTL checks cover primitive and nested aggregate constants. Constants
are available when a concrete design needs them; no equality-with-constant
module is currently planned.

## Completed balanced Boolean reduction

`Reduction` constructs and certifies a balanced hierarchy over any finite
family of same-typed inputs from a certified binary operation and certified
identity source. Empty families instantiate the identity, singleton families
are direct wires, and internal nodes recursively reduce two nearly equal
halves before applying the binary child. The tree construction proves both its
leaf count and recursive balance; generic schedules prove structural
uniqueness in left/right/combine order.

`All` instantiates that machinery with bit AND and constant true. Its public
contract deliberately does not expose tree parenthesization: it uses the
ordinary Lean recursion `every` and states that the result is true exactly
when every indexed input is true. A private certification bridge proves the
balanced structural reduction implements that natural contract. Direct FIRRTL
checks cover empty, singleton, and five-input hierarchies without adding a
cocotb target.

## Completed recursive equality

`Equality T` has two `T` inputs and one bit result. Its natural contract uses
the generic recursive value function `SignalType.equal`; the public law states
that the result is true exactly when the two Lean values are equal. The bit
case wraps the closed equality primitive. Vector and tuple structures split
both inputs into immediate components, recursively instantiate Equality for
corresponding components, and feed the indexed family of result bits into
`All`. This preserves aggregate hierarchy and does not impose a global
flattening order. Certification covers structural existence, schedule-based
uniqueness, and refinement for empty and nonempty aggregates. Lean and direct
FIRRTL checks cover bits, empty tuples, vectors, and nested tuples.

## Completed generic vector concatenation

`VectorConcat T leftWidth rightWidth` joins two vectors of `T` without
flattening their elements. Its natural contract uses `Fin.addCases`: left
elements occupy the indices below `leftWidth`, and right elements occupy the
remaining indices. The structure uses one splitter for each input and one
combiner for the result. Certification proves existence, schedule-based
uniqueness, and refinement; public index laws expose both halves. Lean and
direct FIRRTL checks cover either empty half, two nonempty halves, and
aggregate element types.

## Completed binary-to-one-hot decoding

`BinaryToOneHot width` interprets bit index `i` with weight `2 ^ i` and
produces `2 ^ width` result bits. Its contract is numeric: output index `i` is
true exactly when `i` is the natural-number value of the input. The certified
structure is recursive rather than an equality bank. Width zero emits the
one-element constant `[true]`; each successor width splits off the leading
bit, reconstructs and decodes the tail, masks the decoded vector with the bit
and its inverse, and joins the two halves with `VectorConcat`. Public theorems
connect the numeric law to the recursive decoder. Lean and direct FIRRTL checks
cover widths zero through three; no cocotb target is needed for this module.

## Completed combinational mux tree

`CombMuxTree T indexWidth` takes `2 ^ indexWidth` values of type `T` and an
LSB-first bit-vector index. Its natural contract returns the value at the
numeric index. The recursive structure partitions the values with the generic
certified `VectorSplit`, rebuilds the lower-index selector bits using ordinary signal
  adapters, evaluates two smaller mux trees, and selects between their results
with `Mux T`. `VectorSplit` is the reusable inverse-shaped counterpart of
`VectorConcat`, rather than a mux-specific adapter. Certification proves
existence, schedule-based uniqueness, and refinement. Lean and direct FIRRTL
checks cover index widths zero through three and both bit and aggregate values.

## Completed generic register bank

`RegisterBank T addressWidth` contains `2 ^ addressWidth` entries with one
synchronous write port and one combinational read port. Its natural contract
stores a vector of `T`: reading returns the currently addressed pre-update
entry, while an enabled write replaces exactly one next-state entry and all
others remain unchanged. The structure decodes the write address with
`BinaryToOneHot`, gates the global write enable per entry, instantiates one
generic `EnabledRegister T` per entry, combines their outputs, and reads through
`CombMuxTree T`. The state correspondence relates the contract vector
pointwise to that register family. Certification proves structural existence,
schedule-based uniqueness, and refinement, and public laws expose read,
selected-write, and retention behavior. Lean checks, direct FIRRTL conversion,
and a four-entry cocotb test cover initialization, reads, writes, retention,
and same-address read-before-write behavior. The implementation uses a private
named child-instance type rather than nested sums, keeps construction witnesses
private, and shares `BitVector.toIndex` as the generic numeric interpretation
used by the decoder, mux tree, and register bank.

## Completed LSB-first numeric indexing

Numeric bit vectors now use the conventional hardware ordering: vector index
`i` has weight `2 ^ i`, so index zero is the least-significant bit.
`BitVector.toNat` and `toIndex` recurse by removing the highest-index bit.
`BinaryToOneHot` and `CombMuxTree` follow the same hierarchy directly: their
recursive children receive the lower-index bits and the current high bit
selects between equal output/value halves. RegisterBank addresses inherit this
interpretation through those generic contracts, without reversal wiring or a
bank-specific conversion. Asymmetric checks and the generated RegisterBank
simulation distinguish this convention from the former MSB-first ordering.

## Completed increment arithmetic foundation

The closed XOR bit primitive has a natural Boolean contract and a numeric law
relating XOR and AND to the sum of two input bits. `HalfAdder` composes one XOR
and one AND child behind two named inputs and independent `sum` and `carry`
contract rules. Its public laws expose the Boolean results and the arithmetic
identity `sum + 2 * carry = left + right` without mentioning child structure.
Its two output schedules and all construction witnesses remain private. Lean
truth-table checks and direct FIRRTL rendering cover both the primitive and
composite module.

## Completed combinational increment

`Increment width` has one LSB-first bit-vector input and result. Its contract is
the natural modular arithmetic operation: the result's numeric value is the
input value plus one modulo `2 ^ width`. The certified implementation fixes an
initial carry to true and recursively processes the lower-index bits before a
HalfAdder for the current highest-index bit, so carry flows from low to high.
The carry-aware recursion, schedules, state correspondence, and construction
witnesses are private implementation details. Public laws expose both the
result vector and its modular numeric meaning. Lean checks cover width zero,
one-bit overflow, asymmetric multi-bit carry propagation, and full-width
overflow; FIRRTL checks confirm the recursive HalfAdder hierarchy and bit
ordering. No separate simulation target is needed for this combinational module.

## Completed certified FIFO pointer control

`FifoPointerControl addressWidth` defines the natural combinational boundary
between FIFO pointer state and the eventual FIFO structure. Its LSB-first read
and write pointers contain `addressWidth` address bits followed by one wrap
bit. The contract exposes both addresses, valid/ready flow control, and
explicit read/write advance enables. Equal complete pointers mean empty;
equal addresses with different wrap bits mean full. Transfer behavior is
non-fall-through, so a full FIFO does not accept a simultaneous replacement
and an empty FIFO does not bypass a simultaneous input.

The natural contract and its public laws remain independent of the certified
structure. Structurally, each extended pointer is split directly into bits;
only its address bits are recombined. One generic Equality compares the two
addresses and one primitive equality compares the wrap bits. AND/NOT logic
then derives empty, full, ready, valid, and advance signals. There is no
redundant whole-pointer comparison or one-element wrap vector. The same
structure works when `addressWidth = 0`.

Schedules, child identities, existence construction, uniqueness, and
refinement remain private. Lean and direct FIRRTL checks cover asymmetric
pointers, empty and full states, simultaneous transfers, and zero address
width. Reset is deliberately absent because this module owns no state. The
enclosing FIFO resets both pointer registers equally, from which this control
naturally reports empty.

## Completed generic synchronous-reset registers

`ResetRegister T resetValue` is a certified generic composition of
`Constant T`, `Mux T`, and `Register T`. It exposes current state and loads the
configured constant when reset is high, otherwise loading its ordinary input.
`EnabledResetRegister T resetValue` adds enable/hold selection around that
module, so reset has highest priority, enable loads, and disable retains.
Neither module adds reset behavior to primitives: reset is ordinary synchronous
data-path logic evaluated on the existing clock.

Both contracts state their next-state behavior directly, independent of the
hierarchy. Public laws cover reset, loading, and retention; schedules and
construction proofs remain private. Checks instantiate both modules for bits,
vectors, and named tuples, including reset priority. Configured reset values
are part of emitted module identities, preventing differently configured
definitions from colliding.

## Completed generic enabled-reset counter

`EnabledResetCounter width resetValue` is a certified LSB-first modular
counter with synchronous reset. Its natural contract exposes current state and
defines next state directly: reset has highest priority, enable applies
`Increment.incrementValue`, and otherwise the value is retained. The public
numeric law relates enabled updates to addition modulo `2 ^ width`.

The structure has exactly two children. The current output of
`EnabledResetRegister (.vector width .bit) resetValue` feeds `Increment width`,
whose result returns to the register's value input. Enable and reset connect
directly to the register. All schedules, child identities, construction,
correspondence, uniqueness, and refinement details are private. Contract,
structural, and FIRRTL checks cover reset priority, retention, carry
propagation, rollover, and width zero. No counter-specific primitive was added.

## Completed certified generic FIFO

`Fifo T addressWidth` is the primary pointer-and-storage FIFO implementation.
Its natural contract state contains read and write pointers plus a vector of
entries. The contract directly describes valid/ready observations, the oldest
visible value, pointer advancement, and accepted writes without mentioning
the child hierarchy. Synchronous reset has priority in both pointer updates,
making the following state empty; storage is not cleared.
Because reset is synchronous, current-cycle outputs and any accepted bank
write use the pre-edge state; reset wins only in the pointer next states.

The structure has exactly four children: two zero-reset
`EnabledResetCounter (addressWidth + 1)` pointers, `FifoPointerControl`, and
`RegisterBank T addressWidth`. Certification maps the three contract-state
fields onto those three state-owning children; schedules and all
construction/refinement details remain private. Checks cover ordering,
boundary stalls, simultaneous transfers, carry and rollover, reset, and the
one-entry `addressWidth = 0` case, plus structural uniqueness and FIRRTL.

The older no-reset behavior vocabulary is owned by `NoResetFifo`; its
recursive positive-depth implementation is `SerialDepthFifo`. The canonical
`Fifo` name refers only to the scalable resettable implementation.

## Completed generic FIFO behavioral proof

The canonical `Fifo T addressWidth` now has a logical queue view derived from
its public contract state. Circular extended-pointer distance defines
occupancy; reading the register-bank entries from the read address defines
contents. A reachable-state invariant bounds occupancy by
`2 ^ addressWidth`.

Contract-only proofs establish reset clearing, invariant preservation,
empty/full equivalence, capacity, exact enqueue append, oldest-value dequeue,
simultaneous transfer ordering, stalls, wraparound, and the one-entry
`addressWidth = 0` case. A shared contract-independent runner folds
deterministic steps over finite input lists; a reset-aware FIFO transition
layer gives those observations their queue meaning and lifts the cycle theorem
to arbitrary executions. On reset-free traces it proves
exact conservation and, from empty, that accepted outputs are a prefix of
accepted inputs. The proof does not inspect the FIFO hierarchy or its private
certification machinery.

## Reset-synchronized behavioral contracts

Add a second contract form for exact cycle-by-cycle behavior after synchronous
reset. This contract is independent of `ModuleCycleContract`: a module may
have only a cycle contract, only a reset-synchronized contract, both, or other
contract forms added later.

The reset contract owns an arbitrary Lean specification-state type. Its state
does not need to resemble structural state, and its public certification does
not require or expose a mapping between them. Given the same concrete inputs,
the specification and structure must produce matching outputs on corresponding
cycles after reset has established a common behavioral starting point. Because
reset is synchronous, the reset cycle itself may still observe pre-reset
structural state; required matching begins on the following cycle. A later
reset establishes a fresh comparison point in the same way.

Specification outputs are shaped like module outputs, but every leaf bit is a
ternary expectation: zero, one, or `dontCare`. Matching is recursive over bits,
vectors, and named tuples. `dontCare` relaxes only the value of that bit on that
particular cycle; it does not permit latency changes or matching an output on a
different cycle. This generic expectation and matching foundation is now
implemented independently of contracts in `Foundation/SignalExpectation.lean`.

Certification is stated directly against multi-cycle `ModuleStructure`
execution, so it does not depend on a cycle contract. For modules that already
have `ModuleCycleCertified`, provide a reusable constructor that may use its
evaluator, state correspondence, and refinement proof to establish the reset
contract. That constructor is an optional proof technique and is absent from
the resulting reset certificate's public requirements.

The contract-only semantics are complete. `ModuleResetContract` defines the
reset input, arbitrary specification state, reset state, and ordinary step.
Its trace begins unsynchronized, leaves outputs unconstrained before and on a
reset cycle, checks corresponding ordinary cycles after synchronization, and
supports repeated resets. Generic nil, cons, append, split, length,
synchronization, and pre-reset-prefix laws are established without mentioning
module structure or certification.

`ModuleResetCertified` is also complete. It packages structure, reset contract,
structural totality, and the universal statement that every structural
execution is accepted. Totality prevents a structure with no solutions from
satisfying refinement vacuously and generically supplies finite executions for
every initial structural state and input trace. Because acceptance is
unconstrained before reset, refinement gives the intended behavior from
arbitrary initial structural state; generic suffix laws expose matching after
an initial reset or after a reset following any prefix. No cycle contract,
evaluator, schedule, structural-state mapping, or uniqueness proof is stored in
this certificate.

The canonical FIFO now has a contract-only reset specification. Its state is
the natural Lean queue `List T`, reset establishes `[]`, and ordinary cycles
derive input-ready, output-valid, and head payload expectations directly from
that queue and capacity `2 ^ addressWidth`. Payload is `dontCare` while empty.
The total step handles stalls and each enqueue/dequeue combination; generic
laws prove the four cases, capacity preservation from every bounded state, and
bounded synchronization after reset, including resets following arbitrary
prefixes. `Modules/FifoInterface.lean` owns the shared ports, allowing this
contract to remain independent of the structural FIFO and all cycle-contract
and certification machinery.

The canonical FIFO structure is now directly certified against that reset
contract. From any initial structural state, the proof uses the existing cycle
certificate to obtain a corresponding cycle state but requires no initial
reachability invariant. Outputs remain unconstrained before and on reset;
reset establishes zero pointers, boundedness, and empty logical contents.
Every ordinary cycle thereafter matches ready/valid/ternary payload
expectations and the List queue update, while later resets re-establish the
same alignment. All correspondence and induction witnesses are private;
`Fifo.resetCertified` exposes only `ModuleResetCertified`, including its
structural-totality guarantee.

Direct backend validation now emits a configured four-entry pointer FIFO with
the shared nested tuple/vector payload fixture. Register-bank naming propagates
that payload metadata through its aggregate combiner as well as its storage and
read path. A reproducibly seeded cocotb stream independently randomizes input
valid and output ready, compares every accepted output immediately with the
oldest accepted input, then forces downstream readiness and verifies bounded
complete drainage and an empty FIFO.

This milestone is complete. No next development goal has been selected; future
near-term work should be added here only when there is a concrete, agreed need
for it.

## Long-term RISC-V direction

A possible much later application is a small RV32I CPU made by directly
porting a simple configuration of PicoRV32 into Silean. The intended
correctness boundary is architectural instruction retirement rather than
correspondence between the original and ported implementations' internal
cycles or state-machine state. The Sail model is an independent architectural
specification against which to verify the port; it is not the source design.
The provisional construction hierarchy, specification-blackbox staging
boundary, and ideas for each module's appropriate behavioral specification
are recorded in `docs/PicoRV32ModuleHierarchy.md`.
The proposed first top-level child interfaces, state ownership, acyclic signal
flow, and implementation staging are recorded in
`docs/PicoRV32TopLevelPlan.md`; its remaining interface choices must be
reviewed before implementation begins.

The locally available `sail-riscv32-lean` repository is a candidate upstream
specification dependency when this work becomes timely. It contains the
type-correct Lean translation of the official Sail RISC-V model, including
RV32 decode, architectural state, instruction execution, memory effects, and
traps. It is currently generated, very large, unpolished, and described by its
authors as non-executable, so integrating it is deliberately not near-term
work.

Before depending on it, make a small feasibility study around one ordinary
RV32I instruction. Check Lean and `lean-sail` version compatibility, isolate a
small stable wrapper for the architectural observations we require, and assess
proof and build performance. If direct use is practical, keep the generated
model as an external dependency rather than copying it into Silean. Otherwise,
use it as the authoritative source for a clean RV32I-facing specification and
prove a bridge to that interface. Initial CPU verification should exclude
extensions, interrupts, privileged behavior, and exceptional memory cases
until the base retirement relation is established.

Likely reusable modules needed while porting the simple PicoRV32 configuration
are:

- `FullAdder` and generic fixed-width `Add`, followed by a shared `AddSub`
  datapath;
- generic `BitwiseAnd`, `BitwiseXor`, and, if useful in compositions,
  `BitwiseNot`;
- fixed-width unsigned and signed less-than comparison, alongside the existing
  generic equality;
- logical-left, logical-right, and arithmetic-right shifting, initially with
  the iterative organization used by a simple PicoRV32 configuration rather
  than assuming a barrel shifter;
- a generic register bank with multiple combinational read ports and one
  synchronous write port, with RISC-V's hardwired zero register kept in a
  CPU-specific wrapper;
- one-hot or priority family selection for PicoRV32's decoded control signals,
  chosen according to the decoder validity guarantee;
- clean static bit-vector slicing, concatenation, extension, and permutation
  support for instruction fields and immediates; and
- possibly a reusable single-outstanding ready/valid transaction holder once
  the memory-controller boundary is understood during the port.

Arithmetic is the likely first foundation: `FullAdder`, `Add`, and their
generic proofs unlock PC updates, address calculation, arithmetic instructions,
subtraction, and comparisons. Do not design a generic monolithic ALU in
advance; keep PicoRV32-specific decode and operation selection in the CPU until
the port demonstrates a genuinely reusable boundary.

Each architectural goal ends with a plain-language review, focused timing,
full Lean verification, and relevant external simulation.
