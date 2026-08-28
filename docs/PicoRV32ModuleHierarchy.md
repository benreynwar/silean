# PicoRV32 port module hierarchy

This document is a provisional module plan for directly porting a simple
RV32I configuration of PicoRV32 into Silean. It is not a claim that the
original Verilog already has these module boundaries. PicoRV32 deliberately
keeps most decode, datapath, memory, and control logic in one module; the
boundaries below identify pieces that can have natural contracts and be
developed independently without changing the intended design.

“Contract” in this document does not mean that every module receives a
`ModuleCycleContract`. Contract form follows the abstraction boundary. Pure
datapath modules may naturally use cycle contracts; a memory controller needs
a protocol property over multiple cycles; and the complete CPU needs an
instruction-retirement relation over traces. New contract forms should be
introduced when those statements cannot be expressed naturally by the
existing ones.

The concrete first-pass top-level child interfaces and state ownership are
refined in `PicoRV32TopLevelPlan.md`.

The direct port preserves existing `picorv32.v` module, port, register, and
wire names in its structural interface. Friendlier Lean views belong in
specifications and theorems rather than replacing source names. Proposed child
instances that do not exist in the monolithic Verilog are explicitly marked as
new boundaries in the top-level plan.

The exact initial parameter values are fixed in `PicoRV32TopLevelPlan.md`.
Misalignment and illegal-instruction trapping are enabled.

## Proposed hierarchy

```text
PicoRV32
├── control : PicoRV32Control                  stateful main RTL block
│   └── reusable shift/add/select logic as needed
├── mem     : PicoRV32Memory                   stateful memory RTL region
│   ├── LoadDataFormatter
│   └── StoreDataFormatter
├── decoder : PicoRV32Decoder                  stateful decoder RTL region
├── cpuregs : PicoRV32Regs                     stateful register-file region
│   └── MultiReadRegisterBank (32-bit, 2 reads)
│       ├── EnabledRegister (one per entry)
│       ├── BinaryToOneHot
│       └── CombMuxTree (one per read port)
├── alu     : PicoRV32Alu                      combinational ALU region
│   ├── AddSub (32-bit)
│   │   └── Add
│   │       └── FullAdder (one per bit)
│   │           ├── HalfAdder
│   │           └── primitive bit logic
│   ├── Equality
│   ├── UnsignedLessThan
│   ├── SignedLessThan
│   ├── BitwiseAnd
│   ├── BitwiseOr
│   └── BitwiseXor
└── rvfi    : PicoRV32Rvfi                     stateful formal observer
```

This is a proof and construction hierarchy, not necessarily the final emitted
FIRRTL hierarchy. Small wrappers may be inlined later if keeping them visible
has no explanatory value.

## Top-level and CPU-specific modules

### `PicoRV32`

Owns the externally visible instruction/data memory handshake, reset, trap or
fault indication, and eventual retirement observation. It connects the
decoder, controller, register file, ALU, shifter, memory interface, PC, and
operand/result registers.

Its primary specification should not be a cycle contract reproducing the
implementation state machine. It should relate the externally observable
trace to a sequence of RV32I architectural transitions: source register
values, destination write, old and new PC, and any memory effect. Internal
cycles that do not retire an instruction cause no architectural step, so the
specification remains independent of how many implementation cycles an
instruction takes. This retirement contract may eventually use Sail through a
narrow wrapper, but Sail is not needed to construct the port.

### `PicoRV32Decoder`

Owns the source's registered decoder state and produces the decoded instruction class,
register indices, immediate, ALU/branch operation, memory width and signedness,
and a legality indication required by the chosen configuration. Its structural
outputs may remain close to PicoRV32's one-hot decoded signals rather than
introducing an unrelated instruction representation.

The contract should give a natural Lean decode function. Useful public laws
identify the fields and immediate for each supported RV32I encoding, establish
the meaning of the legality result, and establish any one-hot or mutual-
exclusion fact relied upon by downstream selectors.

### `PicoRV32Alu`

Combines reusable arithmetic, comparison, and bitwise children and selects the
result required by PicoRV32's decoded control signals. It may expose both a
32-bit result and a one-bit comparison result, matching the original datapath.

Its contract should be a direct function of the operation and operands. Public
laws should state each operation independently. The implementation proof may
use decoder exclusivity, but the contract should define behavior explicitly
for every operation value rather than relying on Verilog `case` assumptions.

### `PicoRV32Control`

Owns the ported fetch, operand-load, execute, iterative-shift, store, load, and
trap states, datapath registers, and registered control flags that cross those states. It tells
the datapath which values to capture and tells the memory interface which
transaction to request.

If an exact state-machine cycle contract is helpful while porting, it may state
the next control state and commands for each current state, decoded instruction
class, datapath condition, and memory handshake result. That is proof support,
not necessarily the controller's most useful public specification. Its useful
higher-level properties are temporal: a command is held or advanced exactly as
required, requests and responses are not lost or duplicated, and retirement
occurs only at a completed instruction boundary. Architectural instruction
correctness belongs to the enclosing CPU proof, not to this controller alone.

### `PicoRV32Memory`

Ports PicoRV32's single-outstanding memory state machine. It turns instruction
fetch, data-load, and data-store commands into the external valid/ready
protocol and returns completed read data. It must preserve the address,
write-data, byte mask, and instruction/data classification for as long as the
external request is stalled.

Its contract should describe transaction acceptance and completion directly.
Important laws are request stability under backpressure, at most one
outstanding request, exactly one completion for each accepted command, and the
absence of a write request for reads. Prefetch and compressed-instruction
special cases are absent from the initial configuration.

## Reusable state and datapath modules

### `MultiReadRegisterBank T addressWidth readPorts`

Extends the existing single-read `RegisterBank` with a fixed finite family of
combinational read addresses and values sharing one synchronously written
storage vector.

Its natural contract state is `Vector T (2 ^ addressWidth)`. Every read output
is the pre-update value at its address; an enabled write replaces exactly the
selected entry in the next state. Reads must not be described in terms of the
internal mux trees.

### `PicoRV32Regs`

Instantiates a 32-entry, 32-bit, two-read `MultiReadRegisterBank` and adds the
RV32I `x0` rule.

Its contract should state that either read address zero produces zero, writes
to address zero have no effect, other enabled writes update exactly their
selected register, and reads observe pre-update state. Keeping this rule in a
wrapper preserves the generic meaning of the underlying bank.

### `FullAdder`

Adds two bits and a carry-in, producing a sum bit and carry-out.

The Boolean contract should be accompanied by the arithmetic law
`sum + 2 * carryOut = left + right + carryIn`. Its structure should reuse the
existing `HalfAdder` and primitive bit logic.

### `Add width`

Adds two LSB-first vectors with a carry-in and produces the low `width` result
bits plus carry-out. Width zero should have a natural definition rather than a
special unsupported case.

The contract should use ordinary modular natural-number addition. Public laws
should cover the result modulo `2 ^ width`, carry-out, and the full arithmetic
identity. Ripple construction and intermediate carries remain private.

### `AddSub width`

Shares an adder between addition and two's-complement subtraction, selected by
one control bit. It may expose carry/borrow information only if a real consumer
needs it.

The contract should state modular addition when `subtract = 0` and modular
subtraction when `subtract = 1`. The implementation can invert the right
operand and use the select bit as carry-in, but that identity should not leak
into the behavioral interface.

### `UnsignedLessThan width`

Produces one bit stating whether the first LSB-first vector denotes a smaller
natural number than the second.

The contract should use the shared `BitVector.toNat` interpretation. Its proof
may reuse an adder carry/borrow result or a recursive most-significant-
difference construction.

### `SignedLessThan width`

Compares two width-bit two's-complement values.

The contract should use a clearly named signed interpretation function and
state ordinary integer less-than. Width zero needs an explicit natural
meaning. Public lemmas should connect sign-bit difference and same-sign
unsigned comparison if those facts are used by the structure.

### `BitwiseAnd`, `BitwiseXor`, and `BitwiseNot`

Apply the corresponding Boolean operation recursively to any `SignalType`, as
`BitwiseOr` already does. If the CPU only needs vectors initially, the generic
contract and shared leafwise implementation should nevertheless avoid adding
CPU-specific versions.

Each contract is pointwise recursive signal-value logic. Certification should
reuse `LeafwiseComposition`; module-named facts that are generally about
signal values belong in the generic signal-logic namespace.

### Shift modules

`ShiftLeftStep`, `ShiftRightLogicalStep`, and `ShiftRightArithmeticStep`
perform a fixed structural shift, including the appropriate zero or sign fill.
They are reusable combinational children inside `PicoRV32Control`. The source
control block continues to own `reg_op1`, `reg_sh`, and the shift-state
transition; do not introduce a separate stateful shifter interface.

Step-module contracts should use direct vector indexing. `PicoRV32Control`
should prove that repeated shift-state transitions terminate with the
mathematical RV32 shift result. Do not require the architectural CPU proof to
reason about that internal sequence once the final-result theorem is
established.

### `LoadDataFormatter`

Selects a byte or halfword from a 32-bit returned memory word and performs
signed or unsigned extension; word loads pass through unchanged.

Its contract should use byte-address offset, access width, and signedness to
state the exact 32-bit result. Misaligned behavior should be outside the
contract's valid-input predicate or explicitly represented, matching the
chosen initial CPU configuration.

### `StoreDataFormatter`

Turns a 32-bit store value, byte-address offset, and access width into aligned
32-bit write data and a four-bit byte-enable mask.

Its contract should state which output byte corresponds to each enabled lane,
that disabled lanes are irrelevant, and the exact mask for byte, halfword, and
word stores. Misaligned requests should be handled in the same explicit manner
as loads.

### Family selection

PicoRV32 often selects a result with a family of decoded Boolean conditions.
A reusable `OneHotSelect` is appropriate if the decoder contract proves
exactly one applicable condition. Otherwise use a `PrioritySelect` with an
explicit ordering and default. These are distinct contracts and should not be
blurred into a selector whose behavior is unspecified for realistic inputs.

## Static instruction wiring

Instruction slicing, concatenation, sign extension, zero extension,
replication, and immediate-bit permutation are static connectivity. Prefer
expressing these through general signal layouts/adapters rather than inventing
active primitives. Add a named module such as `SignExtend` only when its
natural contract and repeated use make the hierarchy or proofs clearer.

## Specification blackboxes and completion status

Top-level work should not wait for every reusable child structure. A planned
module may first be used through its real ports and natural specification,
using whichever contract form matches that boundary. Parent proofs should be
parameterized by the relevant behavioral guarantee and should not inspect
child structure or private proof schedules. This may require modular
composition support for contract forms other than `ModuleCycleContract`.

This gives two meaningful completion levels:

1. **Composition verified:** the CPU or parent satisfies its specification
   assuming the stated child behavioral guarantees.
2. **Structurally verified:** every such assumption has been discharged by a
   concrete certified Silean hierarchy.

A specification blackbox is proof staging, not a new permissive hardware
primitive and not a claim that arbitrary behavior is correct. FIRRTL simulation
requires a separate temporary behavioral implementation or external module
until the real structure exists. That backend substitution must not become
part of the semantic contract.

The first likely bottom-up path is `FullAdder` → `Add` → `AddSub` and
comparison. In parallel, the decoder, controller, and top-level retirement
organization can be developed against appropriate specification blackboxes. A
monolithic generic ALU should not be designed in advance; `PicoRV32Alu`
remains CPU-specific until another concrete consumer demonstrates a reusable
boundary.
