import Silean.Semantics.BoundaryTrace
import Silean.Semantics.StructuralEquations

namespace Silean

/-! # Implementation-independent traces of a module body

A `ModuleBody` fixes one layer of interfaces and wiring without choosing any
child implementations.  `ModuleBody.Step` records the parent boundary and all
immediate child boundaries for one aligned cycle.  A body trace is only a list
of those observations: it contains no structural state, child implementation,
or behavioral claim.

`WiringHolds` is deliberately separate from the trace data.  It states that
the bundled observations obey the body's existing simultaneous wiring
equations.  Module-specific composition theorems may combine this fact with
arbitrary predicates on the projected child `BoundaryTrace`s.
-/

namespace ModuleBody

variable {body : ModuleBody}

/-- Parent and immediate-child boundary observations for one common cycle of
an uninstantiated module body. -/
@[ext] structure Step (body : ModuleBody) where
  parent : BoundaryStep body.ports
  child : (name : body.instancePorts.Name) →
    BoundaryStep (body.instancePorts.ports name)

/-- The parent-output values dictated by the body's wiring for this
observation. -/
def Step.wiredParentOutputs (step : body.Step) : body.ports.outputs.Values :=
  fun output =>
    (body.wiring.moduleOutput output).value step.parent.inputs
      (fun child => (step.child child).outputs)

/-- One child's input values dictated by the body's wiring for this
observation. -/
def Step.wiredChildInputs (step : body.Step)
    (name : body.instancePorts.Name) :
    (body.instancePorts.ports name).inputs.Values :=
  body.wiring.childInputValues step.parent.inputs
    (fun child => (step.child child).outputs) name

/-- All parent-output and child-input values in one body observation agree
with the permanent `ModuleBody.wiring`. -/
def Step.WiringHolds (step : body.Step) : Prop :=
  step.parent.outputs = step.wiredParentOutputs ∧
    ∀ name, (step.child name).inputs = step.wiredChildInputs name

namespace Step.WiringHolds

theorem parent_outputs {step : body.Step} (holds : step.WiringHolds) :
    step.parent.outputs = step.wiredParentOutputs :=
  holds.1

theorem parent_output {step : body.Step} (holds : step.WiringHolds)
    (output : body.ports.outputs.Label) :
    step.parent.outputs output = step.wiredParentOutputs output :=
  congrFun holds.1 output

theorem child_inputs {step : body.Step} (holds : step.WiringHolds)
    (name : body.instancePorts.Name) :
    (step.child name).inputs = step.wiredChildInputs name :=
  holds.2 name

theorem child_input {step : body.Step} (holds : step.WiringHolds)
    (name : body.instancePorts.Name)
    (input : (body.instancePorts.ports name).inputs.Label) :
    (step.child name).inputs input = step.wiredChildInputs name input :=
  congrFun (holds.2 name) input

end Step.WiringHolds

/-- A finite, cycle-aligned bundle of parent and immediate-child boundary
observations. -/
abbrev Trace (body : ModuleBody) := List body.Step

namespace Trace

/-- Project the parent boundary trace. -/
def parent (trace : body.Trace) : BoundaryTrace body.ports :=
  trace.map Step.parent

/-- Project one immediate child's boundary trace. -/
def child (trace : body.Trace) (name : body.instancePorts.Name) :
    BoundaryTrace (body.instancePorts.ports name) :=
  trace.map fun step => step.child name

@[simp] theorem parent_nil (body : ModuleBody) :
    parent ([] : body.Trace) = [] :=
  rfl

@[simp] theorem parent_cons (step : body.Step) (trace : body.Trace) :
    parent (step :: trace) = step.parent :: trace.parent :=
  rfl

@[simp] theorem child_nil (body : ModuleBody)
    (name : body.instancePorts.Name) :
    child ([] : body.Trace) name = [] :=
  rfl

@[simp] theorem child_cons (step : body.Step) (trace : body.Trace)
    (name : body.instancePorts.Name) :
    child (step :: trace) name = step.child name :: trace.child name :=
  rfl

@[simp] theorem parent_length (trace : body.Trace) :
    trace.parent.length = trace.length := by
  simp [parent]

@[simp] theorem child_length (trace : body.Trace)
    (name : body.instancePorts.Name) :
    (trace.child name).length = trace.length := by
  simp [child]

theorem mem_parent_of_mem {trace : body.Trace} {step : body.Step}
    (member : step ∈ trace) : step.parent ∈ trace.parent :=
  List.mem_map_of_mem (f := Step.parent) member

theorem mem_child_of_mem {trace : body.Trace} {step : body.Step}
    (name : body.instancePorts.Name) (member : step ∈ trace) :
    step.child name ∈ trace.child name :=
  List.mem_map_of_mem (f := fun candidate => candidate.child name) member

/-- Every cycle bundled in the trace obeys the body's wiring. -/
def WiringHolds (trace : body.Trace) : Prop :=
  ∀ step, step ∈ trace → step.WiringHolds

@[simp] theorem wiringHolds_nil (body : ModuleBody) :
    WiringHolds ([] : body.Trace) := by
  intro step member
  cases member

@[simp] theorem wiringHolds_cons_iff
    (step : body.Step) (trace : body.Trace) :
    WiringHolds (step :: trace) ↔ step.WiringHolds ∧ trace.WiringHolds := by
  simp only [WiringHolds, List.mem_cons]
  constructor
  · intro holds
    exact ⟨holds step (Or.inl rfl), fun later member =>
      holds later (Or.inr member)⟩
  · rintro ⟨head, tail⟩ candidate (rfl | member)
    · exact head
    · exact tail candidate member

namespace WiringHolds

theorem step {trace : body.Trace} (holds : trace.WiringHolds)
    {candidate : body.Step} (member : candidate ∈ trace) :
    candidate.WiringHolds :=
  holds candidate member

/-- Sequence-level form of all parent-output wiring equations. -/
theorem parent_outputs {trace : body.Trace} (holds : trace.WiringHolds) :
    trace.parent.outputs = trace.map Step.wiredParentOutputs := by
  induction trace with
  | nil => rfl
  | cons first rest induction =>
      rw [wiringHolds_cons_iff] at holds
      simp only [parent_cons, BoundaryTrace.outputs_cons, List.map_cons]
      rw [holds.1.parent_outputs, induction holds.2]

/-- Sequence-level form of all input wiring equations for one child. -/
theorem child_inputs {trace : body.Trace} (holds : trace.WiringHolds)
    (name : body.instancePorts.Name) :
    (trace.child name).inputs =
      trace.map (fun step => step.wiredChildInputs name) := by
  induction trace with
  | nil => rfl
  | cons first rest induction =>
      rw [wiringHolds_cons_iff] at holds
      simp only [child_cons, BoundaryTrace.inputs_cons, List.map_cons]
      rw [holds.1.child_inputs name, induction holds.2]

end WiringHolds

end Trace

end ModuleBody

end Silean
