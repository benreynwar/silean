import Silean2.FoundationsH
import Silean2.Modules.Not.NotH

namespace Silean2.Modules.Not.Internals

open Silean2.Foundations
open Silean2.Modules.Not
open Silean2.Modules.Not.NotFromNand

theorem depsSound : DepsSound notSpec childSpecs := by
  simp [DepsSound]
  intro outputKey inputKey pbn
  exact wholeDepSetsRequireAllInputs outputKey inputKey

theorem hasSolution : childSpecs.HasSolution := by
  intro inputs
  let makeValues (input : notPorts.InputValues) : BodyValues notFromNand := {
    values := { inputs := input, outputs := notFunction input }
    childValues := fun _ => {
      inputs := fun _ => input x
      outputs := notFunction input
    }
    valid := by
      constructor <;> intros <;> rfl
  }
  refine ⟨inputs.map makeValues, ?_, ?_⟩
  · simp only [BodyTrace.trace, PortTrace.inputs, List.map_map]
    change inputs.map (fun input => input) = inputs
    exact List.map_id inputs
  · intro childKey
    change ∀ values ∈ BodyTrace.childTrace (inputs.map makeValues) childKey,
      Nand.nandFunction values.inputs = values.outputs
    intro values member
    obtain ⟨bodyValues, bodyMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨input, _, rfl⟩ := List.mem_map.mp bodyMember
    funext outputKey
    simp [makeValues, Nand.nandFunction, notFunction]

theorem childSpecsImplySpec : ChildSpecsImplySpec notSpec childSpecs := by
  intro trace childSpecsMatch
  change ∀ values ∈ trace.trace, notFunction values.inputs = values.outputs
  intro values member
  obtain ⟨bodyValues, bodyMember, rfl⟩ := List.mem_map.mp member
  have childMatches := childSpecsMatch (0 : Fin 1)
  change ∀ values ∈ trace.childTrace (0 : Fin 1),
    Nand.nandFunction values.inputs = values.outputs at childMatches
  have nand := childMatches (bodyValues.childValues (0 : Fin 1)) (List.mem_map.mpr ⟨bodyValues, bodyMember, rfl⟩)
  funext outputKey
  rw [bodyValues.valid.1 outputKey]
  change (!(bodyValues.values.inputs x)) = (bodyValues.childValues (0 : Fin 1)).outputs Nand.result
  rw [← nand]
  simp only [Nand.nandFunction]
  simp only [bodyValues.valid.2 (0 : Fin 1) Nand.left]
  simp [notFromNand, getSourceValue]

theorem notFromNandCertValid : ModuleBodyCertValid notSpec childSpecs :=
  ⟨depsSound, hasSolution, childSpecsImplySpec⟩

end Silean2.Modules.Not.Internals
