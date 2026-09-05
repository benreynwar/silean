# FullAdder authoring review

This is a step-by-step review of `Silean/Modules/FullAdder/FullAdder.lean` and
`Silean/Modules/FullAdder/FullAdderCertified.lean` as an example of the module-authoring
experience. The first file is the hardware-designer-facing description; the
second contains the more conventional Lean certification. This document
records which parts carry useful design or proof information, which parts are
mechanical noise, and which general abstractions may make both files clearer.

The aim is not merely to minimize line count. The important hardware and
behavioral argument should remain visible, while declarations and proofs that
Lean can derive reliably should not distract the reader.

## `module_design` pilot outcome

The separate port, instance, wiring, and naming commands proved useful for
discovering the required generated API, but they formed an implicit protocol:
each command consumed names generated invisibly by the preceding command. The
fixed-module authoring surface now replaces that protocol with one
self-contained declaration:

```lean
module_design FullAdder where
  ports {
    input left : .bit,
    input right : .bit,
    input carryIn : .bit,
    output sum : .bit,
    output carryOut : .bit }

  instances {
    operands := HalfAdder.design,
    carry := HalfAdder.design,
    combineCarry := Primitives.orDesign }

  wiring {
    outputs {
      .sum := carry.sum,
      .carryOut := combineCarry.output }
    instance (.operands) {
      .left := input.left,
      .right := input.right }
    instance (.carry) {
      .left := operands.sum,
      .right := input.carryIn }
    instance (.combineCarry) {
      .left := operands.carry,
      .right := carry.carry }
  }
```

It generates the same ordinary typed declarations as the lower-level
commands, plus `naming` and a reducible `design : Naming.NamedModule` bundle.
Each child is another design bundle, so its structure and recursive naming
cannot be paired incorrectly. Module, port, and fixed-instance names default
exactly to their declaration labels; explicit `name` modifiers remain
available. Ordinary constructor parameters automatically contribute to the
emission specialization through `ToModuleParameter`, so generic modules do not
repeat `.signalType` and `.natural` metadata. Explicit key overrides remain for
unusual cases. Contracts and certifications are not part of this bundle.

`HalfAdder` and `FullAdder` form the dependency-complete fixed pilot.
`EnabledRegister` validates ordinary parameters and component naming, while
`RegisterBank` validates mixed fixed and indexed child families. Their
contracts and certifications remain separate, and their existing correctness
proofs compile unchanged. Fresh structured-FIFO and register-bank FIRRTL was
byte-identical before intentionally adopting declaration labels as emitted
family names and dropping the unneeded `structural` variants; this checked
generic and indexed recursive naming independently of those key simplifications.

An indexed family states both its index type and its executable order. Its
emitted name is an explicit function of that index:

```lean
storage (index : Fin entryCount in Enumeration.fin entryCount)
  (name := s!"entry_{index.val}") := EnabledRegister.design element
```

The design command normally declares its ports inline. A module such as
`RegisterBank`, whose indexed port labels have a useful handwritten
`Enumeration`, instead reuses that typed boundary without hiding it in a port
DSL:

```lean
boundary (RegisterBank.ports element addressWidth readCount)
  (naming := RegisterBank.Naming.ports element addressWidth readCount)
```

In both forms, `module_design` owns the children, wiring, concrete structure,
recursive default naming, and `NamedModule` bundle. The lower-level commands
remain its implementation machinery and are still appropriate for recursive
or programmatically constructed designs; they are no longer needed as a chain
of declarations for these ordinary parameterized modules.

## `module_ports` pilot evaluation

The first authoring command was implemented and piloted on `HalfAdder`, generic
`EnabledRegister`, `VectorConcat`, and the PicoRV ALU. `HalfAdder` now reaches
the same generated API through `module_design`; the command remains directly
used by the other pilots. Its concrete syntax is:

```lean
module_ports ports (signalType : SignalType)
    with (typeNaming : SignalTypeNaming signalType :=
      SignalTypeNaming.positional signalType) where
  input data (schema := typeNaming) : signalType,
  input enable : .bit,
  output q (schema := typeNaming) : signalType
```

It generates ordinary `Input` and `Output` inductives with `Enumeration`
instances, `inputMap`, `outputMap`, `ports`, and either `Naming.ports` alone or
both `Naming.portsWithNaming` and its positional default. Focused checks verify
that all of these declarations have the same dependent types and values as the
handwritten forms.

The pilot found and corrected two surface-language problems before wider use:

- indentation alone did not delimit arbitrary Lean signal-type terms reliably,
  so port entries are explicitly comma-separated; and
- declaration keywords such as `input`, `output`, and `naming` must not be
  registered as global Lean keywords, because that prevents existing fields
  and definitions with those names from parsing. The command parses them as
  identifiers and reports a focused error when they are misspelled.

The generated declarations remain available to completion, `#check`, and
`#print`, and all existing downstream proofs compile without changes. A
navigation request for a generated declaration necessarily leads to the
`module_ports` invocation rather than a handwritten definition body; `#print`
is therefore the escape hatch when a Lean user needs to inspect the expansion.
This is an unavoidable but limited cost of declaration-generating syntax.

The initial two declarations remove 39 lines and add 18 across their module
diffs, including new imports and `open` commands. The additional migrations
remove the separated port and naming blocks from `VectorConcat` and the PicoRV
ALU. More importantly, each port shape and emitted name now appear together at
the start of the module. Focused clean builds remain interactive for the small
modules: approximately 1.8 seconds for `HalfAdder`, 1.9 seconds for
`EnabledRegister`, and 2.3 seconds for `VectorConcat` on the development
machine. The ALU itself remains roughly eight seconds, with no material change
attributable to port generation.

The completion pass also added empty input or output directions and multiple
independent component-naming parameters. Focused checks cover both features.
The command deliberately does not generate indexed label families with custom
enumeration proofs, such as `RegisterBank`, and it should not duplicate a
boundary derived from another reusable abstraction, such as `Constant`. Those
modules retain ordinary declarations. Supporting most ordinary modules is more
valuable than forcing every module through one surface form.

The original recommendation was to retain this small command while evaluating
the other sections. The completed review refined that conclusion: its
generated declarations remain useful as a lower-level implementation API, but
ordinary fixed modules should present one self-contained `module_design`
declaration. Recursive and programmatically constructed modules should still
use ordinary Lean when that is clearer than forcing them through surface
syntax.

## Review criteria

For each section, ask:

1. Does a hardware designer need it to understand the module?
2. Does a proof reviewer need it to understand what is proved?
3. If neither does, can it be derived generically without weakening the
   trusted proof boundary?

Prefer, in order, deletion, an ordinary generic definition or theorem, a
better constructor, controlled simplification, and finally a macro or tactic.

## Imports and introductory description

The design file imports only authoring, contract-description, child-design,
and naming modules. Schedule derivation, child certifications, and proof
tactics live exclusively in `FullAdderCertified.lean`.

The introductory comment should remain. It concisely states both the natural
one-bit full-adder behavior and the implementation strategy of two half adders
and one OR gate.

## Ports

The input and output labels, their directions, their signal shapes, and their
emitted names are all important interface information. They should remain
visible, but they currently appear in separate declarations:

- the `Input` inductive;
- the `Output` inductive;
- `inputMap`;
- `outputMap`;
- `ports`; and
- `Naming.ports` near the end of the file.

These declarations repeat the same label set. Introduce a general
`module_ports` command that declares each port once and generates the ordinary
Lean inductives, enumerations, signal maps, `ModulePorts`, and
`ModulePortsNaming` definitions.

A FullAdder declaration using the pilot command is:

```lean
module_ports ports where
  input left : .bit,
  input right : .bit,
  input carryIn (name := "carry_in") : .bit,
  output sum : .bit,
  output carryOut (name := "carry_out") : .bit
```

The emitted name defaults to the Lean identifier when `name` is omitted. Use
explicit overrides rather than an implicit camel-case conversion policy.

The command supports arbitrary signal shapes and separate component naming,
as demonstrated by `EnabledRegister` and `VectorConcat`. It does not generate
parameterized labels such as:

```lean
input readAddress (reader : Fin readCount) : addressType,
input payload (schema := payloadNaming) : payloadType
```

The optional `components` modifier supplies a `SignalTypeNaming` for the
contents of a vector or named tuple. Without it, the existing positional
default applies. Parameterized labels usually come with meaningful enumeration
code, as in `RegisterBank`; keeping those definitions explicit is clearer than
making this port command into a general inductive-type and enumeration DSL.

This is surface-language compression only. The command should generate the
same ordinary declarations used by current proofs, so it does not change the
foundational representation.

Complete `ModuleNaming` remains separate. Its module key and child-instance
names describe the implementation hierarchy rather than the boundary ports.
A similar combined declaration for instances may be considered when that
section is reviewed.

## Behavioral values and cycle contract

`sumValue` and `carryValue` are natural Lean descriptions of the full-adder
behavior. They are useful to module users and make the later correctness
argument readable, so they should remain ordinary, prominent definitions.

The rest of the section expresses important information but repeats substantial
contract scaffolding. The information a reader should see is:

- the module has no state;
- it has independently callable `sum` and `carryOut` rules;
- both rules read `left`, `right`, and `carryIn`;
- each rule writes its corresponding output; and
- the targets use `sumValue` and `carryValue`.

The current declarations additionally require the author to write:

- a separate `Rule` inductive and `Enumeration` instance;
- explicit rule signatures that duplicate the types of the selected ports;
- handwritten read/write group declarations;
- the association from rule labels to rule definitions;
- the empty state rule and output-coverage proof; and
- nearly identical unfolding proofs for the public `...Rule_holds_iff`
  characterizations.

The implemented general cycle-contract declaration gives FullAdder this form:

```lean
module_cycle_contract cycleContract for ports where
  state := emptySignalMap

  output_rule sum where
    reads := [left, right, carryIn]
    writes := { sum := sumValue left right carryIn }

  output_rule carryOut where
    reads := [left, right, carryIn]
    writes := { carryOut := carryValue left right carryIn }

  state_rule where
    reads := []
    next := {}
```

This preserves rule boundaries, read and write sets, and behavioral equations
as visible design information. The declaration infers rule signatures from
the named ports and generates the `Rule` labels, private named groups,
concrete rules, contract assembly, exact coverage proof, and
mechanical `...Rule_holds_iff` laws. The explicit empty `state_rule` makes clear
that stateless modules use the same form as stateful ones.

For a larger rule already expressed as an ordinary Lean value, the declaration
can register it without inventing another expression language:

```lean
output_rule apply := outputRule
```

The ALU uses this form. Its selection, target, and public behavioral law remain
ordinary Lean definitions; the declaration supplies rule identity, state,
coverage, and contract assembly.

The generated `sumRule_holds_iff` and `carryOutRule_holds_iff` statements are
valuable public proof APIs. Their names and statements follow directly from
the visible rule declarations; their mechanical unfolding bodies stay hidden.

Do not replace the contract with one opaque `inputs → outputs` function. The
separate output rules are useful when a parent gives an explicit structural
schedule for only the child results it needs.

## Child-instance boundaries

The design and proof sides now make two deliberately separate choices. The
hardware description selects concrete child structures:

```lean
module_instances instancePorts for ports where
  operands := HalfAdder.moduleStructure,
  carry := HalfAdder.moduleStructure,
  combineCarry (name := "combine_carry") :=
    ModuleStructure.primitive Primitives.or
```

This generates only structural declarations:

- the `Instance` inductive;
- its `Enumeration` instance;
- the `InstancePorts` map;
- the emitted instance-name function used by `ModuleNaming`;
- the `EndpointContext`; and
- the computable `structuralChildren` mapping.

As with module ports, an omitted emitted name defaults to the Lean identifier.
An explicit `(name := ...)` modifier handles deliberate differences without an
implicit case-conversion policy.

The proof-oriented file separately associates every child with a contract and
certificate:

```lean
module_child_certifications childContracts for body where
  operands := HalfAdder.certification,
  carry := HalfAdder.certification,
  combineCarry := Primitives.orCertified.certification
```

This generates `childContracts`, `certifiedChildren`, and a theorem proving
that every certified child's structure is exactly the structure selected by
`module_instances`. A mismatched certificate therefore fails at this boundary.
The certification's dependent type is the sole source of both the child
structure and selected contract. There is no separate contract override. Every
ordinary reusable module should consequently expose a canonical
`certification`; its `certified` bundle is useful derived packaging, not a value
that parent declarations must unpack again.
The structural command continues to support generic and indexed families. The
design side of `RegisterBank`, for example, states its significant executable
enumeration explicitly:

```lean
storage (index : Fin (entryCount addressWidth) in
    Enumeration.fin (entryCount addressWidth))
  (name := s!"entry_{index.val}") := EnabledRegister.moduleStructure element
```

Requiring the enumeration makes the significant order visible rather than
assuming a typeclass order. The command enumerates a nested sum of the fixed
and indexed entries in source order, then uses the generic
`Enumeration.relabel` operation to transport it to the generated `Instance`
type. The mechanically generated inverse proofs establish completeness and
absence of duplicates. Only module parameters used by family index types are
carried by `Instance`; for `RegisterBank` those are `addressWidth` and
`readCount`, not the unrelated `element` type.

The generated structural vocabulary is namespace-visible rather than Lean
`private`, because a separate certification file must refer to the instance
type, body, and selected structures. The substantive `implements` proof still
quantifies over abstract `layerChildren : ChildStructures body childContracts`
and sees only child contracts. Concrete `certifiedChildren` are used later to
instantiate that already-completed proof.

`FullAdder` is the two-file pilot. `FullAdder.lean` is an 81-line design file
containing the boundary, visible child hierarchy and wiring, natural behavior,
cycle contract, and derived naming. `FullAdderCertified.lean` contains child
certifications, schedules, the parametric correctness argument, final
certification, and derived correctness theorems. `HalfAdder` and the AND, OR,
and XOR primitives were split at the same boundary. The other primitives used
by generic naming are likewise separated into definition-only and certified
files. Consequently, the complete transitive import closure of the FullAdder
design—not merely its direct imports—contains no cycle-certification or
scheduling code.

## Structural wiring

Traditional Verilog or VHDL commonly declares an intermediate wire and then
connects that name at both its producing and consuming instances. Silean's
current `Wiring` instead defines the source of every parent output and child
input directly. This avoids naming and mentioning a connection twice, makes
total wiring natural, and should remain the foundational representation.

The handwritten presentation was nevertheless noisy: all child connections
shared one pattern match, and every source repeated `context.moduleInput` or
`context.instanceOutput`. The implemented `module_wiring` command groups the
same complete port map by sink:

```lean
module_wiring wiring for context where
  outputs {
    .sum := carry.sum,
    .carryOut := combineCarry.output }
  instance (.operands) {
    .left := input.left,
    .right := input.right }
  instance (.carry) {
    .left := operands.sum,
    .right := input.carryIn }
  instance (.combineCarry) {
    .left := operands.carry,
    .right := carry.carry }
```

This keeps all connectivity explicit while presenting each child's complete
port map together. `input.left` denotes a parent input and `operands.sum`
denotes a child output. Braces delimit groups without making `outputs` a global
Lean keyword. Constructor patterns on the left keep dependent and indexed
ports available; an indexed source uses forms such as
`readMux(port)[.result]` or `decodeSplit[index]`.

The command generates the same ordinary total `Wiring` value, the mechanical
`ModuleBody`, and the concrete `ModuleStructure`. Lean's generated dependent
pattern matches check that every sink is covered and that every driver has the
same signal shape. Its original pilots covered fixed `FullAdder`, generic
stateful `EnabledRegister`, and the fixed-plus-indexed families of
`RegisterBank`; `FullAdder` now reaches the same generated `body` through
`module_design`. Their existing schedules and certification proofs compile
unchanged; no structural-child implementation is made available to those
proofs.

Across those pilots, the directive removes 21 lines from `FullAdder`, 9 from
`EnabledRegister`, and 24 from `RegisterBank` relative to their preceding
`module_instances` forms. More importantly, each child's entire input map is
now a separate visible group. The indexed register-bank pilot exercises
indexed child destinations, indexed child sources, value-labelled combiner
ports, and parameterized parent ports. Its emitted FIRRTL retained the exact
pre-migration output. The later `module_design` migration intentionally
changes only the literal default module, port, and instance names. After
normalizing those explicit renames, the old and new FullAdder FIRRTL are
byte-identical. The full Lean build and all four FIRRTL-to-Verilog cocotb tests
pass.

Use `:=`, not `<-` or `←`. Assignment-style `:=` matches Lean declarations and
structure fields, whereas the arrow syntax normally suggests monadic binding
and execution order. Wiring denotes simultaneous connectivity, not sequential
computation.

The command is deliberately a thin elaborator over ordinary Lean definitions.
It expands the concise sources and lets the kernel-checked `Wiring` type reject
missing endpoints, nonexistent ports, or signal-shape mismatches. Focused
checks inspect the generated definitions for both fixed and indexed children.

Do not require explicit internal wires. They would duplicate direct
producer-to-consumer connections and introduce a new structural identity with
little value. A future syntax may permit optional local source aliases when a
large design has repeated, complicated sources, but those aliases should not
be foundational wire nodes unless a concrete requirement demands that.

## Child cycle contracts

The `childContracts` mapping states which behavior the parent proof may assume
at every physical child boundary. This remains meaningful proof-design
information: a concrete child structure may satisfy several contracts, and the
parent must deliberately choose the abstraction it uses.

The design-side `module_instances` intentionally does not choose a contract.
The proof-side declaration makes that choice explicitly:

```lean
module_child_certifications childContracts for body where
  operands := HalfAdder.certification,
  carry := HalfAdder.certification,
  combineCarry := Primitives.orCertified.certification
```

It checks that:

- every declared child has exactly one cycle contract;
- each contract's ports match the corresponding physical child boundary;
- no undeclared child is mentioned; and
- parameterized child families are covered exhaustively.

Indexed families repeat only the binder type needed to elaborate their
certificate:

```lean
module_child_certifications childContracts (element : SignalType)
    (addressWidth : Nat) for body element addressWidth where
  storage (_index : Fin (entryCount addressWidth)) :=
    EnabledRegister.certification element
```

Do not infer a contract merely from a structure. Only a supplied certification
may determine the contract, because its type explicitly proves the selected
structure implements that particular contract. The generated structure-match
theorem additionally ensures that it certifies the implementation selected in
the design file.

## Parametric layer-certification envelope

The beginning and end of the layer-certification section contain mechanical
framework plumbing around the substantive `implements` proof. Automation here
must be conservative because this is the proof connecting the hardware
structure to its behavioral contract.

The essential visible choices are:

- the structural `body` being certified;
- the parent `cycleContract`;
- the `childContracts` the proof may assume;
- the derived schedules establishing structural existence and uniqueness; and
- the chosen relation between contract state and structural state.

A completed module uses the assembly declaration after its ordinary
module-specific proof:

```lean
module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements
```

The separate `implements` theorem introduces abstract
`layerChildren : ChildStructures body childContracts`; it remains parametric
in that family and cannot inspect the concrete `certifiedChildren` used later.
The declaration only assembles already-visible proof ingredients and derives:

- the final `ModuleCycleCertifiedLayer`;
- the certification of the independently declared concrete structure;
- the derived public `certified` bundle; and
- projection lemmas identifying that bundle's structure and contract.

It deliberately does not invent the state correspondence or automate the
`implements` goal. That proof is
the substance of module correctness and should remain recognizable as normal
Lean. Within it, focused tactics may hide routine transport through framework
types only when their useful result remains explicitly named and stated, for
example:

```lean
child_contract_fact operandSumValue :
    (proposal.2 .operands).outputs .sum =
      HalfAdder.sumValue (inputs .left) (inputs .right) from
    (childMatch .operands).1 using
    HalfAdder.sum_of_evaluatesTo _ _ _ _
```

The visible proof should continue to show the meaningful chain of child facts
and how they establish each parent output and the next-state relation.

Avoid invisible local proof configuration such as:

```lean
attribute [local simp] body wiring
```

Child-contract normalization should use a controlled tactic that explicitly
knows which `body`, `wiring`, and `context` it is unfolding. This keeps changes
to the simplifier from silently altering unrelated portions of the proof.

The governing rule is: automation may hide how a routine fact is transported
through framework types, but it must not hide which behavioral facts are used
or how those facts establish the parent behavior.

## Child facts inside `implements`

The FullAdder proof has the right high-level shape: obtain public child
contract evaluations, state meaningful equations about child outputs, and use
those equations to establish the parent behavior. Keep the five named facts:

- `operandSumValue`;
- `operandCarryValue`;
- `finalSumValue`;
- `secondCarryValue`; and
- `combinedCarryValue`.

Together they clearly describe the standard two-half-adder implementation.
The remaining noise is how the framework refers to those values and obtains
their proofs.

Add an ordinary `ProposedValues.childOutput` accessor so proofs can write:

```lean
proposal.childOutput .operands .sum
```

instead of exposing the pair projection and child proposal internals:

```lean
(proposal.2 .operands).outputs .sum
```

Extend `child_contract_fact` with a common-case form that selects the child
evaluation by instance label:

```lean
child_contract_fact operandSumValue at .operands :
    proposal.childOutput .operands .sum =
      HalfAdder.sumValue (inputs .left) (inputs .right)
using HalfAdder.sum_of_evaluatesTo _ _ _ _
```

The tactic may supply `(childMatch .operands).1` and normalize the declared
parent wiring, but the complete resulting behavioral equation remains visible.
Retain the lower-level form accepting an explicit evaluation for stateful or
otherwise unusual children.

`combinedCarryValue` currently makes the parent unpack the OR contract's
`EvaluatesTo` evidence, select `Primitives.OrRule.apply`, and convert its
`Holds` result manually. Reusable primitives should instead expose public laws
such as:

```lean
Primitives.orOutput_of_evaluatesTo
```

Parents should reason through these contract-level laws and should not need to
know a child's internal rule label. Apply this API convention consistently to
reusable primitive contracts when needed, rather than teaching the parent
tactic special cases for OR.

The FullAdder pilot no longer uses `attribute [local simp] body wiring`.
Instead, each child-fact tactic passes `body`, `wiring`, and `context`
explicitly to a controlled normalization step. Proof success therefore does
not depend on an invisible change to the local simplifier.

`derive_empty_state_child_matches` remains appropriate: it hides only routine
state-correspondence plumbing and returns public child-contract evaluations.
It does not hide any behavioral conclusion used by the FullAdder proof.

## Parent behavior inside `implements`

The remainder of `implements` connects the parent outputs to their structural
drivers, rewrites with the five named child facts, and proves the resulting
expressions equal `sumValue` and `carryValue`. This is the core,
module-specific correctness argument and should remain ordinary visible Lean.

Do not introduce a FullAdder-oriented tactic for these branches. In
particular, the proof that the OR of the two half-adder carries equals the
three-input `carryValue` is genuine behavioral reasoning rather than framework
plumbing.

Two small generic improvements remain appropriate. First, add semantic
accessors to the structural-solution hypothesis so code can replace:

```lean
have boundary := satisfies.1
```

with a meaningful form such as:

```lean
have boundary := satisfies.moduleOutputs
```

or obtain one equation directly:

```lean
have sumBoundary := satisfies.moduleOutput .sum
```

These accessors merely name existing evidence; they do not prove or infer any
connection.

Second, the stateless layer-certification constructor may generate the outer
packaging:

```lean
refine ⟨SignalMap.emptyValues, ?_, trivial⟩
constructor
...
· rfl
```

The visible proof can then focus on the parent output rules. It must still show
which structural boundary equation and which child behavioral facts establish
each rule.

## Public behavioral laws

The public laws split into mechanical projections of the cycle contract and
genuine FullAdder mathematics.

The `module_cycle_contract` declaration generates the mechanical rule
characterizations:

```lean
sumRule_holds_iff
carryOutRule_holds_iff
```

These public laws live with the contract because they describe its behavior,
not how a particular structure is certified. More specialized consequences
of evaluation can remain ordinary theorems when a module needs them.

For a rule writing several outputs, the generated characterization conjoins
the visible equations in declaration order. This was checked independently of
FullAdder so the command is not accidentally specialized to one-output rules.

Keep `numeric_value` as an ordinary module-specific theorem. It states the
important mathematical fact that the two Boolean results encode the sum of
three input bits, and its exhaustive Boolean proof is already concise.

Keep `numeric_value_of_evaluatesTo` as the user-facing consequence of contract
evaluation. Its proof should visibly combine the generated output laws with
`numeric_value`, while also using implicit evaluation arguments. These two
numeric theorems are useful behavior, not framework noise.

## Design bundles and recursive naming

The `module_design` pilot removes the separate `FullAdder.Naming` section.
Naming is generated from information already local to the complete design
declaration:

- the declaration label is the default module name;
- port labels are the default port names;
- `Instance` constructors are the default fixed-instance names; and
- each selected child design carries naming for its own exact structure.

All defaults are literal: there is no automatic case conversion. A module,
port, or instance may use an explicit `name` modifier when its emitted name
really should differ. The primitive design bundles pair each primitive
structure with the existing primitive FIRRTL naming in the same way.

The generated `Naming.NamedModule` is a presentation bundle, not a new
structural foundation. `ModulePorts`, `ModuleBody`, and `ModuleStructure`
remain independent of emission names, and contracts remain independent of the
bundle. A caller can therefore construct alternative naming for a structure
when needed, while the ordinary parent-authoring path gets a safe default
without repeating child naming.

Generic modules will require parameterized design builders, and indexed child
families will require an explicit function for names that cannot be obtained
from one fixed constructor label. Those are the next validation cases; they
should extend the one self-contained declaration rather than restore an
author-visible chain of partial macros.

## Validation against other module families

The authoring model was compared with `EnabledRegister`,
`RegisterBank`, recursive `Register`, recursive `Equality`, and the PicoRV ALU.
It generalizes well, with the following requirements and limits.

### Stateful modules

The migration of `EnabledRegister` confirms that the implemented
`module_cycle_contract` supports state and ordinary parameters. It expresses:

- an explicit state map;
- output rules that read selected state fields; and
- a state rule that reads inputs and defines each next-state field.

Stateless contracts remain the zero-field case of the same general
declaration.

The EnabledRegister state correspondence is meaningful: its contract state
corresponds to the storage child's contract and structural state. That mapping
must remain visible. Only its mechanical witness transport and certificate
assembly should be derived.

### Indexed instance families

`RegisterBank` now confirms in working code that parameterized child families
and their enumeration order are first-class. Its decoder, split, gate family,
storage family, combiner, and read-mux family are declared once, in the order
used for enumeration and generated naming.

Grouped wiring should accept indexed destinations and sources, for example:

```lean
instance storage index
  value  := input.writeValue
  enable := gate(index).output
```

Schedule syntax must also expose family calls concisely, while preserving their
meaningful order. It may generate mapped rule occurrences already understood
by `derive_rule_schedules`; it must not hide when a whole family is exercised.

The RegisterBank correspondence between each abstract entry and one indexed
storage child remains important proof information and should stay explicit.

### Recursive composition abstractions

Generic `Register` and aggregate `Equality` are built by existing recursive
leafwise and reduction abstractions. Forcing them into an expanded ordinary
instance declaration would duplicate or expose machinery those abstractions
already capture.

The new commands are optional surface front ends that generate foundational
objects for ordinary structural layers. They are not a mandatory replacement
for reusable recursive composition mechanisms. Port declarations, contract
declarations, public evaluation laws, and certification-envelope helpers may
still apply independently to recursive modules.

Equality's bit layer is a good ordinary-layer candidate, while its aggregate
layer should retain the generic recursive implementation. A public module
family may therefore mix generated declarations and direct generic
construction at different recursive cases.

### Large combinational modules

The PicoRV ALU should benefit substantially from declaring its ports,
instances, contracts, concrete child certifications, wiring, naming, and rule
orders once. Its explicit wiring and named behavioral equations must remain
visible.

The ALU also has one contract rule writing several outputs. The declaration
already generates its mechanical conjunction of output equations; any more
meaningful ALU-level consequences should remain explicitly chosen public laws.

### Large stateful pilot: DecoderCaptureStage

`DecoderCaptureStage` tests a substantially different shape from FullAdder: it
has four inputs, fourteen registered outputs, twenty-five heterogeneous child
instances, an aggregate thirteen-field enabled register, and a separate reset
register for the branch-class flag. Its substantive proof relates the natural
fourteen-field contract state to those two structural state children.

The completed migration splits the former large mixed source into a concise
`DecoderCaptureStage.lean` hardware/contract/naming file and a separate
`DecoderCaptureStageCertified.lean` proof file. The design file uses the
self-contained `module_design` declaration together with `signal_schema` and
`module_cycle_contract`. The proof file uses
`module_child_certifications`, `module_rule_schedules`, and
`module_cycle_certification`, while retaining the state correspondence and
the entire `implements` argument as ordinary Lean.

This module demonstrates that `module_design` remains readable for a large,
heterogeneous fixed child layer. Recursive and programmatically generated
modules remain the intentional cases for ordinary Lean construction.

Two generally useful additions came from this pilot. Grouped wiring accepts
`from (source)` when the source is an ordinary typed Lean expression. The
cycle-contract declaration accepts `state_rule := existingRule`, allowing a
natural whole-map next-state definition to remain visible rather than being
restated field by field. Both forms are independently covered by authoring
checks.

Instance names now follow their Lean declaration labels by default. The old
snake-case and `slice_...` spellings added no semantic information and are not
duplicated as overrides. The module's structural children, connections,
contract behavior, rule ordering, and substantive proof are unchanged.

### Resulting implementation priorities

The cross-module comparison adds three requirements to the FullAdder-derived
plan:

1. Validate the implemented stateful `module_cycle_contract` declaration on a
   larger multi-output design such as the ALU, then migrate contracts in
   dependency order.
2. Treat indexed instance families and their enumeration order as core
   `module_instances` functionality.
3. Support parameterized naming builders and positional defaults rather than
   assuming every module has one fixed `ModuleNaming`.
