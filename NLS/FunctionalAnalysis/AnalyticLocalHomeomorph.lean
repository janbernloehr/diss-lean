import NLS.FunctionalAnalysis.AnalyticEquivalenceInverse
import Mathlib.Topology.IsLocalHomeomorph

/-! An analytic map whose actual derivative is a Banach equivalence at
every source is a local homeomorphism in the same Banach topologies. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem isLocalHomeomorph_of_analytic_equiv_fderiv (f : E → F)
    (hf : ∀ x, AnalyticAt 𝕜 f x) (e : E → E ≃L[𝕜] F)
    (he : ∀ x, fderiv 𝕜 f x=(e x).toContinuousLinearMap) : IsLocalHomeomorph f := by
  intro x
  have hd : HasStrictFDerivAt f (e x).toContinuousLinearMap x := by
    rw [← he x]
    exact (hf x).hasStrictFDerivAt
  exact ⟨hd.toOpenPartialHomeomorph f,hd.mem_toOpenPartialHomeomorph_source,
    hd.toOpenPartialHomeomorph_coe.symm⟩

end NLS.FunctionalAnalysis
