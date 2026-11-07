import NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse

/-! Analytic inversion between different Banach spaces at an explicitly
identified continuous linear derivative equivalence. -/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_localInverse_of_equiv_fderiv {f : E → F} {x : E}
    (hf : AnalyticAt ℂ f x) (e : E ≃L[ℂ] F) (he : fderiv ℂ f x=e.toContinuousLinearMap) :
    ∃ g : F → E, AnalyticAt ℂ g (f x) ∧ g (f x)=x ∧
      (∀ᶠ y in 𝓝 x, g (f y)=y) ∧ (∀ᶠ z in 𝓝 (f x), f (g z)=z) ∧
      fderiv ℂ g (f x)=e.symm.toContinuousLinearMap := by
  have hs : HasStrictFDerivAt f e.toContinuousLinearMap x := by
    rw [← he]
    exact hf.hasStrictFDerivAt
  let P := hs.toOpenPartialHomeomorph f
  have hP : (P : E → F)=f := hs.toOpenPartialHomeomorph_coe
  have hg : AnalyticAt ℂ P.symm (f x) := by
    have h := P.analyticAt_symm' hs.mem_toOpenPartialHomeomorph_source
      (by rw [hP]; exact hf) (i := e) (by rw [hP]; exact he)
    rw [hP] at h
    exact h
  refine ⟨hs.localInverse _ _ _,hg,hs.localInverse_apply_image,
    hs.eventually_left_inverse,hs.eventually_right_inverse,?_⟩
  exact hs.to_localInverse.hasFDerivAt.fderiv

end NLS.ComplexAnalysis
