import NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse

/-! Analytic inversion over a nontrivially normed field, between different Banach spaces at an explicitly
identified continuous linear derivative equivalence. -/
noncomputable section
open Filter Topology
namespace NLS.FunctionalAnalysis
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem exists_localInverse_of_equiv_fderiv {f : E → F} {x : E}
    (hf : AnalyticAt 𝕜 f x) (e : E ≃L[𝕜] F) (he : fderiv 𝕜 f x=e.toContinuousLinearMap) :
    ∃ g : F → E, AnalyticAt 𝕜 g (f x) ∧ g (f x)=x ∧
      (∀ᶠ y in 𝓝 x, g (f y)=y) ∧ (∀ᶠ z in 𝓝 (f x), f (g z)=z) ∧
      fderiv 𝕜 g (f x)=e.symm.toContinuousLinearMap := by
  have hs : HasStrictFDerivAt f e.toContinuousLinearMap x := by
    rw [← he]
    exact hf.hasStrictFDerivAt
  let P := hs.toOpenPartialHomeomorph f
  have hP : (P : E → F)=f := hs.toOpenPartialHomeomorph_coe
  have hg : AnalyticAt 𝕜 P.symm (f x) := by
    have h := P.analyticAt_symm' hs.mem_toOpenPartialHomeomorph_source
      (by rw [hP]; exact hf) (i := e) (by rw [hP]; exact he)
    rw [hP] at h
    exact h
  refine ⟨hs.localInverse _ _ _,hg,hs.localInverse_apply_image,
    hs.eventually_left_inverse,hs.eventually_right_inverse,?_⟩
  exact hs.to_localInverse.hasFDerivAt.fderiv

end NLS.FunctionalAnalysis
