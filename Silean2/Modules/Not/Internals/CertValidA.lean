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
  sorry

theorem childSpecsImplySpec : ChildSpecsImplySpec notSpec childSpecs := by
  sorry

def notFromNandCertValid : ModuleBodyCertValid notSpec childSpecs :=
  ⟨depsSound, hasSolution, childSpecsImplySpec⟩

end Silean2.Modules.Not.Internals
