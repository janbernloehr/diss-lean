import NLS.FunctionalAnalysis.AnalyticEquivalenceInverse

/-! A flat inverse-chart interface for the analytic inverse theorem. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_openPartialHomeomorph_of_equiv_fderiv {f : E → F} {x : E}
    (hf : AnalyticAt 𝕜 f x) (e : E ≃L[𝕜] F) (he : fderiv 𝕜 f x=e.toContinuousLinearMap) :
    ∃ P : OpenPartialHomeomorph E F, x ∈ P.source ∧ ∀ y : E, P y=f y := by
  have hs : HasStrictFDerivAt f e.toContinuousLinearMap x := by
    rw [← he]
    exact hf.hasStrictFDerivAt
  refine ⟨hs.toOpenPartialHomeomorph f,hs.mem_toOpenPartialHomeomorph_source,?_⟩
  intro y
  exact congrFun hs.toOpenPartialHomeomorph_coe y

end NLS.FunctionalAnalysis
